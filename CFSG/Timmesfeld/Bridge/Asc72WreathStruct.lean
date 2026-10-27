module

public import CFSG.Timmesfeld.Bridge.Asc72WreathDefs
public import CFSG.Timmesfeld.Bridge.Asc72Minimal
import CFSG.GroupTheory.LocalCores.MinimalNormal

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

namespace WreathStruct

variable {G : Type} [Group G] {M : Subgroup G} {r : ℕ} {S : Fin r → Subgroup G}

section Factors

variable {e : ((i : Fin r) → S i) ≃* M}
  (he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : G) = x i)
include he

theorem coe_apply_mulSingle (i : Fin r) (x : S i) : (e (Pi.mulSingle i x) : G) = x := by
  rw [he i (Pi.mulSingle i x) fun j hj => Pi.mulSingle_eq_of_ne hj _, Pi.mulSingle_eq_same]

theorem commute_of_mem_of_ne {i j : Fin r} (hij : i ≠ j) {x y : G} (hx : x ∈ S i)
    (hy : y ∈ S j) : Commute x y := by
  have h := ((Pi.mulSingle_commute hij (⟨x, hx⟩ : S i) (⟨y, hy⟩ : S j)).map e.toMonoidHom).map
    M.subtype
  simp only [Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom, coe_apply_mulSingle he] at h
  exact h

theorem eq_one_of_mem_of_mem {i j : Fin r} (hij : i ≠ j) {x : G} (hi : x ∈ S i) (hj : x ∈ S j) :
    x = 1 := by
  have h : e (Pi.mulSingle i ⟨x, hi⟩) = e (Pi.mulSingle j ⟨x, hj⟩) :=
    Subtype.ext (by rw [coe_apply_mulSingle he, coe_apply_mulSingle he])
  have h2 := congrFun (e.injective h) i
  rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hij] at h2
  exact congrArg Subtype.val h2

theorem le_of_forall_factor_le {H : Subgroup G} (hH : ∀ i, S i ≤ H) : M ≤ H := by
  intro m hm
  obtain ⟨x, hx⟩ := e.surjective ⟨m, hm⟩
  have hxK : x ∈ H.comap (M.subtype.comp e.toMonoidHom) := by
    refine Subgroup.pi_mem_of_mulSingle_mem x fun i => ?_
    show ((e (Pi.mulSingle i (x i)) : M) : G) ∈ H
    rw [coe_apply_mulSingle he]
    exact hH i (x i).2
  have h : ((e x : M) : G) ∈ H := hxK
  rwa [hx] at h

theorem injective_of_ne_bot (hne : ∀ i, S i ≠ ⊥) : Function.Injective S := by
  intro i j hij
  by_contra h
  apply hne i
  rw [eq_bot_iff]
  intro x hx
  exact Subgroup.mem_bot.mpr (eq_one_of_mem_of_mem he h hx (hij ▸ hx))

theorem exists_eq_of_isSimpleGroup (hSM : ∀ i, S i ≤ M) (hsimple : ∀ i, IsSimpleGroup (S i))
    (hSn : ∀ i, ∀ m ∈ M, ∀ x ∈ S i, m * x * m⁻¹ ∈ S i)
    (hC : Subgroup.centralizer (M : Set G) = ⊥) {N : Subgroup G} (hNM : N ≤ M)
    (hNn : ∀ m ∈ M, ∀ n ∈ N, m * n * m⁻¹ ∈ N) (hNs : IsSimpleGroup N) : ∃ k, N = S k := by
  by_contra h
  push Not at h
  have hdisj : ∀ k, N ⊓ S k = ⊥ := by
    intro k
    rcases (Subgroup.isSimpleGroup_iff.mp (hsimple k)).2 (N ⊓ S k) inf_le_right
        ((Subgroup.normal_subgroupOf_iff inf_le_right).mpr fun x s hx hs =>
          Subgroup.mem_inf.mpr ⟨hNn s (hSM k hs) x (Subgroup.mem_inf.mp hx).1,
            (S k).mul_mem ((S k).mul_mem hs (Subgroup.mem_inf.mp hx).2) ((S k).inv_mem hs)⟩)
      with h1 | h1
    · exact h1
    · exfalso
      have hle : S k ≤ N := inf_eq_right.mp h1
      rcases (Subgroup.isSimpleGroup_iff.mp hNs).2 (S k) hle
          ((Subgroup.normal_subgroupOf_iff hle).mpr fun x n hx hn => hSn k n (hNM hn) x hx)
        with h2 | h2
      · exact (Subgroup.isSimpleGroup_iff.mp (hsimple k)).1 h2
      · exact h k h2.symm
  have hcomm : ∀ k, S k ≤ Subgroup.centralizer (N : Set G) := by
    intro k s hs
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have h1 : n * s * n⁻¹ * s⁻¹ ∈ N ⊓ S k := by
      refine Subgroup.mem_inf.mpr ⟨?_, (S k).mul_mem (hSn k n (hNM hn) s hs) ((S k).inv_mem hs)⟩
      have := N.mul_mem hn (hNn s (hSM k hs) n⁻¹ (N.inv_mem hn))
      simpa only [mul_assoc] using this
    rw [hdisj k, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1
  have hN : N ≤ Subgroup.centralizer (M : Set G) :=
    Subgroup.le_centralizer_iff.mpr (le_of_forall_factor_le he hcomm)
  rw [hC] at hN
  exact (Subgroup.isSimpleGroup_iff.mp hNs).1 (le_bot_iff.mp hN)

theorem exists_permHom [M.Normal] (hSM : ∀ i, S i ≤ M) (hsimple : ∀ i, IsSimpleGroup (S i))
    (hSn : ∀ i, ∀ m ∈ M, ∀ x ∈ S i, m * x * m⁻¹ ∈ S i)
    (hC : Subgroup.centralizer (M : Set G) = ⊥) :
    ∃ π : G →* Equiv.Perm (Fin r),
      ∀ g i, (S i).map (MulAut.conj g).toMonoidHom = S (π g i) := by
  have hex : ∀ (g : G) (i : Fin r), ∃ k, (S i).map (MulAut.conj g).toMonoidHom = S k := by
    intro g i
    refine exists_eq_of_isSimpleGroup he hSM hsimple hSn hC ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact ‹M.Normal›.conj_mem x (hSM i hx) g
    · rintro m hm _ ⟨x, hx, rfl⟩
      refine ⟨(g⁻¹ * m * g) * x * (g⁻¹ * m * g)⁻¹, hSn i _ ?_ x hx, ?_⟩
      · have := ‹M.Normal›.conj_mem m hm g⁻¹
        simpa using this
      · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
    · have := hsimple i
      exact MulEquiv.isSimpleGroup ((S i).equivMapOfInjective _ (MulAut.conj g).injective).symm
  choose f hf using hex
  have hinj := injective_of_ne_bot he fun i => (Subgroup.isSimpleGroup_iff.mp (hsimple i)).1
  let _ : MulAction G (Fin r) :=
    { smul := f
      one_smul := fun i => hinj (by
        show S (f 1 i) = S i
        rw [← hf]
        ext x
        simp)
      mul_smul := fun g h i => hinj (by
        show S (f (g * h) i) = S (f g (f h i))
        rw [← hf, ← hf, ← hf, Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc]) }
  exact ⟨MulAction.toPermHom G (Fin r), fun g i => hf g i⟩

end Factors

variable {D : Set G} [Finite G]

theorem exists_swap (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hM : IsMinimalNormal M) {e : ((i : Fin r) → S i) ≃* M}
    (he : ∀ (i : Fin r) (x : (j : Fin r) → S j), (∀ j, j ≠ i → x j = 1) → (e x : G) = x i)
    (hSM : ∀ i, S i ≤ M) (hsimple : ∀ i, IsSimpleGroup (S i))
    (hSn : ∀ i, ∀ m ∈ M, ∀ x ∈ S i, m * x * m⁻¹ ∈ S i) (hr : 2 ≤ r)
    {π : G →* Equiv.Perm (Fin r)}
    (hπ : ∀ g i, (S i).map (MulAut.conj g).toMonoidHom = S (π g i)) {u : G} (hu : u ∈ D) :
    ∃ i j : Fin r, i ≠ j ∧ π u = Equiv.swap i j ∧
      ∀ k : Fin r, k ≠ i → k ≠ j → ∀ x ∈ S k, Commute u x := by
  have := hM.1
  have hne : ∀ k, S k ≠ ⊥ := fun k => (Subgroup.isSimpleGroup_iff.mp (hsimple k)).1
  have hconj : ∀ (g : G) {k : Fin r} {x : G}, x ∈ S k → g * x * g⁻¹ ∈ S (π g k) := by
    intro g k x hx
    rw [← hπ]
    exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
  have hconj' : ∀ (g : G) {k : Fin r} {x : G}, x ∈ S (π g k) → g⁻¹ * x * g ∈ S k := by
    intro g k x hx
    rw [← hπ] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa [MulAut.conj_apply, mul_assoc] using hy
  have huu : u * u = 1 := hS.oddT.mul_self_eq_one hu
  have hπu : π u ≠ 1 := by
    intro h1
    have hker : ∀ g, π g = 1 := by
      have hle : Subgroup.closure D ≤ π.ker := by
        rw [Subgroup.closure_le]
        intro d hd
        obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hu hd)
        rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, h1, mul_one, map_inv,
          mul_inv_cancel]
      intro g
      have hg : g ∈ Subgroup.closure D := by
        rw [hS.gen]
        exact Subgroup.mem_top g
      exact MonoidHom.mem_ker.mp (hle hg)
    have hnorm : (S ⟨0, by omega⟩).Normal :=
      ⟨fun x hx g => by simpa [hker g] using hconj g hx⟩
    rcases hM.2.2 _ hnorm (hSM _) with h | h
    · exact hne _ h
    · apply hne ⟨1, by omega⟩
      rw [eq_bot_iff]
      intro x hx
      have hx0 : x ∈ S ⟨0, by omega⟩ := by
        rw [h]
        exact hSM _ hx
      exact Subgroup.mem_bot.mpr (eq_one_of_mem_of_mem he (by simp [Fin.ext_iff]) hx hx0)
  obtain ⟨i, hi⟩ : ∃ i, π u i ≠ i := by
    by_contra h
    push Not at h
    exact hπu (Equiv.ext h)
  obtain ⟨j, hj⟩ : ∃ j, π u i = j := ⟨_, rfl⟩
  rw [hj] at hi
  have hji : π u j = i := by
    rw [← hj, ← Equiv.Perm.mul_apply, ← map_mul, huu, map_one, Equiv.Perm.one_apply]
  have hij : i ≠ j := fun h => hi h.symm
  obtain ⟨a, haS, ha⟩ : ∃ a ∈ S i, orderOf a = 2 := by
    have heven : 2 ∣ Nat.card (S i) := by
      by_contra hodd
      exact hne i (eq_bot_of_le_of_isSolvable hrad (hSM i) (hSn i)
        (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hodd))))
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 heven
    exact ⟨x, x.2, by rw [Subgroup.orderOf_coe, hx]⟩
  have haa : a * a = 1 := by rw [← pow_two, ← ha, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha
    exact absurd ha (by decide)
  obtain ⟨b, hb⟩ : ∃ b, b = u * a * u⁻¹ := ⟨_, rfl⟩
  have hbS : b ∈ S j := by
    rw [hb, ← hj]
    exact hconj u haS
  have hbb : b * b = 1 := by
    rw [hb, show u * a * u⁻¹ * (u * a * u⁻¹) = u * (a * a) * u⁻¹ by group, haa, mul_one,
      mul_inv_cancel]
  have hab : Commute a b := commute_of_mem_of_ne he hij haS hbS
  have hu'D : a * u * a⁻¹ ∈ D := hS.conj_mem a hu
  have huu' : u * (a * u * a⁻¹) = b * a⁻¹ := by
    rw [hb, hS.oddT.inv_eq hu]
    group
  have hcuu' : Commute u (a * u * a⁻¹) := by
    rw [commute_iff_mul_sq_eq_one huu (hS.oddT.mul_self_eq_one hu'D), huu', pow_two]
    calc b * a⁻¹ * (b * a⁻¹) = b * (a⁻¹ * b) * a⁻¹ := by group
      _ = b * (b * a⁻¹) * a⁻¹ := by rw [hab.inv_left.eq]
      _ = b * b * (a * a)⁻¹ := by group
      _ = 1 := by rw [hbb, haa, inv_one, one_mul]
  have hne' : u ≠ a * u * a⁻¹ := by
    intro h
    have h1 : b * a⁻¹ = 1 := by rw [← huu', ← h, huu]
    have h2 : a ∈ S j := by
      rw [← mul_inv_eq_one.mp h1]
      exact hbS
    exact ha1 (eq_one_of_mem_of_mem he hij haS h2)
  obtain ⟨Y, hY⟩ : ∃ Y : Subgroup G, Y = Subgroup.centralizer (S i : Set G) ⊓
      Subgroup.centralizer (S j : Set G) ⊓ M := ⟨_, rfl⟩
  have hmemY : ∀ y, y ∈ Y ↔ (y ∈ Subgroup.centralizer (S i : Set G) ∧
      y ∈ Subgroup.centralizer (S j : Set G)) ∧ y ∈ M := by
    intro y
    rw [hY, Subgroup.mem_inf, Subgroup.mem_inf]
  have hYM : Y ≤ M := fun y hy => ((hmemY y).mp hy).2
  have hY1 : ∀ k, k ≠ i → k ≠ j → S k ≤ Y := by
    intro k hki hkj x hx
    exact (hmemY x).mpr
      ⟨⟨Subgroup.mem_centralizer_iff.mpr fun s hs =>
          (commute_of_mem_of_ne he (Ne.symm hki) hs hx).eq,
        Subgroup.mem_centralizer_iff.mpr fun s hs =>
          (commute_of_mem_of_ne he (Ne.symm hkj) hs hx).eq⟩, hSM k hx⟩
  have hY2 : ∀ y ∈ Y, Commute (y * u * y⁻¹) u := by
    intro y hy
    obtain ⟨⟨hyi, hyj⟩, -⟩ := (hmemY y).mp hy
    have hya : Commute y a := (Subgroup.mem_centralizer_iff.mp hyi a haS).symm
    have hyb : Commute y b := (Subgroup.mem_centralizer_iff.mp hyj b hbS).symm
    have h1 : y * (u * (a * u * a⁻¹)) * y⁻¹ = u * (a * u * a⁻¹) := by
      rw [huu']
      exact (hyb.mul_right hya.inv_right).mul_inv_cancel
    have h2 := (Commute.conj_iff y).mpr ((Commute.refl u).mul_right hcuu')
    rw [h1] at h2
    exact ((hS.oddT.commute_mul_iff hu hu'D (hS.conj_mem y hu) hne' hcuu').mp h2).1
  have hY3 : ∀ y ∈ Y, u * y * u⁻¹ ∈ Y := by
    intro y hy
    obtain ⟨⟨hyi, hyj⟩, hyM⟩ := (hmemY y).mp hy
    have key : ∀ {k l : Fin r}, π u l = k → y ∈ Subgroup.centralizer (S l : Set G) →
        u * y * u⁻¹ ∈ Subgroup.centralizer (S k : Set G) := by
      intro k l hlk hyl
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have ht : u⁻¹ * s * u ∈ S l := by
        refine hconj' u ?_
        rw [hlk]
        exact hs
      have hyt := Subgroup.mem_centralizer_iff.mp hyl _ ht
      calc s * (u * y * u⁻¹) = u * ((u⁻¹ * s * u) * y) * u⁻¹ := by group
        _ = u * (y * (u⁻¹ * s * u)) * u⁻¹ := by rw [hyt]
        _ = u * y * u⁻¹ * s := by group
    exact (hmemY _).mpr ⟨⟨key hji hyj, key hj hyi⟩, ‹M.Normal›.conj_mem y hyM u⟩
  have hpair : ∀ x ∈ conjOrbit Y u, ∀ z ∈ conjOrbit Y u, Commute x z := by
    rintro _ ⟨y₁, hy₁, rfl⟩ _ ⟨y₂, hy₂, rfl⟩
    have h := (Commute.conj_iff y₂).mpr (hY2 (y₂⁻¹ * y₁) (Y.mul_mem (Y.inv_mem hy₂) hy₁))
    have e1 : y₂ * (y₂⁻¹ * y₁ * u * (y₂⁻¹ * y₁)⁻¹) * y₂⁻¹ = y₁ * u * y₁⁻¹ := by group
    rwa [e1] at h
  have hA : Subgroup.closure (conjOrbit Y u) ⊓ Y = ⊥ := by
    have hnorm_of : ∀ g : G, (∀ n ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y,
        g * n * g⁻¹ ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y) →
        (∀ n ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y,
          g⁻¹ * n * g ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y) →
        g ∈ Subgroup.normalizer ((Subgroup.closure (conjOrbit Y u) ⊓ Y : Subgroup G) : Set G) := by
      intro g h1 h2
      rw [Subgroup.mem_normalizer_iff]
      intro n
      refine ⟨h1 n, fun hn => ?_⟩
      have := h2 _ hn
      rwa [show g⁻¹ * (g * n * g⁻¹) * g = n by group] at this
    have hYnorm : ∀ y ∈ Y, ∀ n ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y,
        y * n * y⁻¹ ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y := by
      intro y hy n hn
      rw [Subgroup.mem_inf] at hn ⊢
      refine ⟨conj_mem_closure ?_ hn.1, Y.mul_mem (Y.mul_mem hy hn.2) (Y.inv_mem hy)⟩
      rintro _ ⟨y', hy', rfl⟩
      exact ⟨y * y', Y.mul_mem hy hy', by group⟩
    have hcent : ∀ k, (k = i ∨ k = j) → ∀ s ∈ S k, ∀ n ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y,
        s * n * s⁻¹ = n := by
      rintro k hk s hs n hn
      obtain ⟨⟨hni, hnj⟩, -⟩ := (hmemY n).mp (Subgroup.mem_inf.mp hn).2
      rcases hk with rfl | rfl
      · rw [Subgroup.mem_centralizer_iff.mp hni s hs, mul_inv_cancel_right]
      · rw [Subgroup.mem_centralizer_iff.mp hnj s hs, mul_inv_cancel_right]
    have hle : M ≤ Subgroup.normalizer
        ((Subgroup.closure (conjOrbit Y u) ⊓ Y : Subgroup G) : Set G) := by
      refine le_of_forall_factor_le he fun k s hs => ?_
      by_cases hk : k = i ∨ k = j
      · refine hnorm_of s (fun n hn => ?_) (fun n hn => ?_)
        · rw [hcent k hk s hs n hn]
          exact hn
        · have h := hcent k hk s⁻¹ ((S k).inv_mem hs) n hn
          rw [inv_inv] at h
          rw [h]
          exact hn
      · push Not at hk
        have hsY := hY1 k hk.1 hk.2 hs
        refine hnorm_of s (hYnorm s hsY) (fun n hn => ?_)
        have h := hYnorm s⁻¹ (Y.inv_mem hsY) n hn
        rwa [inv_inv] at h
    refine eq_bot_of_le_of_isSolvable hrad (M := M) (inf_le_right.trans hYM)
      (fun m hm n hn => (Subgroup.mem_normalizer_iff.mp (hle hm) n).mp hn) ?_
    exact Group.isSolvable_of_comm fun x z =>
      Subtype.ext (commute_of_mem_closure hpair (Subgroup.mem_inf.mp x.2).1
        (Subgroup.mem_inf.mp z.2).1).eq
  have hY6 : ∀ y ∈ Y, Commute u y := by
    intro y hy
    have h : y * u * y⁻¹ * u⁻¹ ∈ Subgroup.closure (conjOrbit Y u) ⊓ Y := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.subset_closure ⟨y, hy, rfl⟩)
        (Subgroup.inv_mem _ (Subgroup.subset_closure (self_mem_conjOrbit Y u))), ?_⟩
      have := Y.mul_mem hy (hY3 _ (Y.inv_mem hy))
      simpa only [mul_assoc] using this
    rw [hA, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  have hcomm : ∀ k : Fin r, k ≠ i → k ≠ j → ∀ x ∈ S k, Commute u x :=
    fun k hki hkj x hx => hY6 x (hY1 k hki hkj hx)
  have hfix : ∀ k, k ≠ i → k ≠ j → π u k = k := by
    intro k hki hkj
    by_contra h
    apply hne k
    rw [eq_bot_iff]
    intro x hx
    have h1 : u * x * u⁻¹ = x := by rw [(hcomm k hki hkj x hx).eq, mul_inv_cancel_right]
    have h2 := hconj u hx
    rw [h1] at h2
    exact Subgroup.mem_bot.mpr (eq_one_of_mem_of_mem he h h2 hx)
  refine ⟨i, j, hij, Equiv.ext fun k => ?_, hcomm⟩
  by_cases hki : k = i
  · rw [hki, Equiv.swap_apply_left, hj]
  · by_cases hkj : k = j
    · rw [hkj, Equiv.swap_apply_right, hji]
    · rw [Equiv.swap_apply_of_ne_of_ne hki hkj, hfix k hki hkj]

end WreathStruct

open WreathStruct in
theorem nonempty_wreathData {G : Type} [Group G] [Finite G] {D : Set G} (hS : Setup G D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {M : Subgroup G}
    (hM : IsMinimalNormal M) (hMs : ¬ IsSimpleGroup M) : Nonempty (WreathData G D M) := by
  have := hM.1
  obtain ⟨r, S, hr1, hSM, hsimple, hSconj, hSnormal, e, he⟩ :=
    CFSG.LocalCores.minimal_normal_simple_factors hM.1 hM.2.1 hM.2.2
  have hSn : ∀ k, ∀ m ∈ M, ∀ x ∈ S k, m * x * m⁻¹ ∈ S k := fun k m hm x hx =>
    (Subgroup.normal_subgroupOf_iff (hSM k)).mp (hSnormal k) x m hx hm
  have hne : ∀ k, S k ≠ ⊥ := fun k => (Subgroup.isSimpleGroup_iff.mp (hsimple k)).1
  have hr2 : 2 ≤ r := by
    by_contra h
    obtain rfl : r = 1 := by omega
    apply hMs
    have hSeq : S 0 = M :=
      le_antisymm (hSM 0) (le_of_forall_factor_le he fun k => by rw [Subsingleton.elim k 0])
    rw [← hSeq]
    exact hsimple 0
  obtain ⟨π, hπ⟩ := exists_permHom he hSM hsimple hSn (centralizer_eq_bot_of_minimal hS hrad hM)
  have hinj := injective_of_ne_bot he hne
  have hnc : ∀ i, ∃ a b : S i, a * b ≠ b * a := by
    intro i
    by_contra h
    push Not at h
    exact hne i (eq_bot_of_le_of_isSolvable hrad (hSM i) (hSn i) (Group.isSolvable_of_comm h))
  have htr : ∀ i j, ∃ g : G, π g i = j := by
    intro i j
    obtain ⟨g, hg⟩ := hSconj i j
    refine ⟨g⁻¹, hinj ?_⟩
    rw [← hπ, hg]
    rfl
  exact ⟨⟨r, hr2, S, hsimple, hnc, hSM, e, he, π, hπ, htr,
    fun u hu => exists_swap hS hrad hM he hSM hsimple hSn hr2 hπ hu⟩⟩

end CFSG.Timmesfeld.Bridge.Asc72
