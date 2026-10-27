module

public import CFSG.Timmesfeld.Bridge.RootStructR2OneTorus
public import CFSG.Timmesfeld.Bridge.RootClosureGen

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped Matrix commutatorElement

namespace RootOne

variable {G : Type} [Group G] {D : Set G}

section Schur

variable {K : Type*} [Field K] {X N N₀ : Subgroup G} {φ : ↥X ≃* Matrix.SpecialLinearGroup (Fin 2) K}
  {θ : (Fin 2 → K) → G}

theorem natQuot_eq_of_mem (hθ : Higman.IsNaturalQuotient φ N N₀ θ) {n : G} {v w : Fin 2 → K}
    (hv : (θ v)⁻¹ * n ∈ N₀) (hw : (θ w)⁻¹ * n ∈ N₀) : v = w := by
  have h1 : (θ v)⁻¹ * θ w ∈ N₀ := by
    have := N₀.mul_mem hv (N₀.inv_mem hw)
    rwa [show (θ v)⁻¹ * n * ((θ w)⁻¹ * n)⁻¹ = (θ v)⁻¹ * θ w by group] at this
  have h2 := hθ.map_add v (w - v)
  rw [add_sub_cancel] at h2
  have h3 : θ (w - v) ∈ N₀ := by
    have := N₀.mul_mem h2 (N₀.inv_mem h1)
    rw [show (θ v * θ (w - v))⁻¹ * θ w * ((θ v)⁻¹ * θ w)⁻¹ = (θ (w - v))⁻¹ by group] at this
    exact inv_mem_iff.1 this
  exact (sub_eq_zero.1 (hθ.eq_zero_of_mem _ h3)).symm

theorem natQuot_exists_smul [CharP K 2] (hθ : Higman.IsNaturalQuotient φ N N₀ θ)
    (hnorm : ∀ n ∈ N, ∀ m ∈ N₀, n * m * n⁻¹ ∈ N₀)
    (hXN₀ : ∀ g ∈ X, ∀ m ∈ N₀, g * m * g⁻¹ ∈ N₀) {h : G} (hhN : ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hhN₀ : ∀ m ∈ N₀, h * m * h⁻¹ ∈ N₀) (hhX : ∀ g ∈ X, Commute h g) :
    ∃ μ : K, ∀ v, (θ (μ • v))⁻¹ * (h * θ v * h⁻¹) ∈ N₀ := by
  classical
  have hex : ∀ v, ∃ w, (θ w)⁻¹ * (h * θ v * h⁻¹) ∈ N₀ := fun v =>
    hθ.exists_eq _ (hhN _ (hθ.mem v))
  choose F hF using hex
  have hadd : ∀ v w, F (v + w) = F v + F w := by
    intro v w
    refine natQuot_eq_of_mem hθ (hF (v + w)) ?_
    set m := (θ v * θ w)⁻¹ * θ (v + w) with hm
    have hm0 : m ∈ N₀ := hθ.map_add v w
    have e : h * θ (v + w) * h⁻¹ = (h * θ v * h⁻¹) * (h * θ w * h⁻¹) * (h * m * h⁻¹) := by
      rw [hm]; group
    have h1 : (θ (F v + F w))⁻¹ * (h * θ (v + w) * h⁻¹) =
        ((θ (F v) * θ (F w))⁻¹ * θ (F v + F w))⁻¹ *
          ((θ (F w))⁻¹ * ((θ (F v))⁻¹ * (h * θ v * h⁻¹)) * θ (F w)) *
          ((θ (F w))⁻¹ * (h * θ w * h⁻¹)) * (h * m * h⁻¹) := by
      rw [e]; group
    rw [h1]
    refine N₀.mul_mem (N₀.mul_mem (N₀.mul_mem (N₀.inv_mem (hθ.map_add _ _)) ?_) (hF w))
      (hhN₀ m hm0)
    have := hnorm _ (N.inv_mem (hθ.mem (F w))) _ (hF v)
    rwa [inv_inv] at this
  have hequiv : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) v,
      F ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ F v := by
    intro g v
    set u := φ.symm g with hu
    have hgu : φ u = g := by rw [hu, MulEquiv.apply_symm_apply]
    have huX : (u : G) ∈ X := u.2
    refine natQuot_eq_of_mem hθ (hF _) ?_
    rw [← hgu]
    set m₃ := (θ ((φ u : Matrix (Fin 2) (Fin 2) K) *ᵥ v))⁻¹ * ((u : G) * θ v * (u : G)⁻¹)
    have hm₃ : m₃ ∈ N₀ := hθ.map_mulVec u v
    set m₄ := (θ ((φ u : Matrix (Fin 2) (Fin 2) K) *ᵥ F v))⁻¹ *
      ((u : G) * θ (F v) * (u : G)⁻¹)
    have hm₄ : m₄ ∈ N₀ := hθ.map_mulVec u (F v)
    have hcomm := (hhX _ huX).eq
    have e : (θ ((φ u : Matrix (Fin 2) (Fin 2) K) *ᵥ F v))⁻¹ *
        (h * θ ((φ u : Matrix (Fin 2) (Fin 2) K) *ᵥ v) * h⁻¹) =
        m₄ * ((u : G) * ((θ (F v))⁻¹ * (h * θ v * h⁻¹)) * (u : G)⁻¹) * (h * m₃⁻¹ * h⁻¹) := by
      have e1 : h * θ ((φ u : Matrix (Fin 2) (Fin 2) K) *ᵥ v) * h⁻¹ =
          h * ((u : G) * θ v * (u : G)⁻¹) * h⁻¹ * (h * m₃⁻¹ * h⁻¹) := by
        simp only [m₃]; group
      rw [e1]
      simp only [m₄]
      calc _ = (θ ((φ u : Matrix (Fin 2) (Fin 2) K) *ᵥ F v))⁻¹ *
            ((h * (u : G)) * θ v * (h * (u : G))⁻¹) * (h * m₃⁻¹ * h⁻¹) := by group
        _ = (θ ((φ u : Matrix (Fin 2) (Fin 2) K) *ᵥ F v))⁻¹ *
            (((u : G) * h) * θ v * ((u : G) * h)⁻¹) * (h * m₃⁻¹ * h⁻¹) := by rw [hcomm]
        _ = _ := by group
    rw [e]
    exact N₀.mul_mem (N₀.mul_mem hm₄ (hXN₀ _ huX _ (hF v))) (hhN₀ _ (N₀.inv_mem hm₃))
  obtain ⟨μ, hμ⟩ := Higman.additive_eq_smul F hadd hequiv
  exact ⟨μ, fun v => hμ v ▸ hF v⟩

end Schur

theorem exists_fixed_mem_coset [Finite G] {N₀ : Subgroup G} (hN₀ : IsPGroup 2 N₀) {h n : G}
    (hp : (orderOf h).Prime) (hp2 : orderOf h ≠ 2) (hhN₀ : ∀ m ∈ N₀, h * m * h⁻¹ ∈ N₀)
    (hn : n⁻¹ * (h * n * h⁻¹) ∈ N₀) : ∃ c : G, n⁻¹ * c ∈ N₀ ∧ h * c * h⁻¹ = c := by
  classical
  have : Fact (orderOf h).Prime := ⟨hp⟩
  set S : Set G := {c | n⁻¹ * c ∈ N₀} with hS
  have hmap : ∀ c ∈ S, h * c * h⁻¹ ∈ S := by
    intro c hc
    have e : n⁻¹ * (h * c * h⁻¹) = (n⁻¹ * (h * n * h⁻¹)) * (h * (n⁻¹ * c) * h⁻¹) := by group
    show n⁻¹ * (h * c * h⁻¹) ∈ N₀
    rw [e]
    exact N₀.mul_mem hn (hhN₀ _ hc)
  have hiter : ∀ k : ℕ, ∀ c : G, (fun c => h * c * h⁻¹)^[k] c = h ^ k * c * (h ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro c; simp
    | succ k ih =>
      intro c
      rw [Function.iterate_succ_apply', ih, pow_succ']
      group
  have hfix : ∀ c ∈ S, (fun c => h * c * h⁻¹)^[orderOf h] c = c := by
    intro c _
    rw [hiter, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  have hcard : Nat.card S = Nat.card N₀ := by
    refine Nat.card_congr
      { toFun := fun c => ⟨n⁻¹ * c.1, c.2⟩
        invFun := fun m => ⟨n * m.1, by show n⁻¹ * (n * m.1) ∈ N₀; simp⟩
        left_inv := fun c => by ext; simp
        right_inv := fun m => by ext; simp }
  have hndvd : ¬ orderOf h ∣ Nat.card S := by
    rw [hcard]
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hN₀
    rw [hk]
    exact fun h' => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h'))
  have : Finite S := Set.toFinite S
  obtain ⟨c, hc, hfc⟩ := RootDegen.exists_fixed_of_prime hmap hfix hndvd
  exact ⟨c, hc, hfc⟩

theorem isPGroup_lineN₀ [Finite G] (a d : G) : IsPGroup 2 (lineN₀ D a d) :=
  (isPGroup_nCore D a).to_le inf_le_left

namespace ModConf

variable {a d x y : G} {C : LineConf D a d x y} {K : Type*} [Field K]
  {φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K}
  {θ₀ θ₁ : (Fin 2 → K) → G} (M : ModConf C φ θ₀ θ₁)
include M

theorem θ₀_zero : θ₀ 0 = 1 := by
  have h := M.nat₀.map_add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

theorem mem_lineN₀_of_scalar {h : G} (hhX : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute h g)
    {μ : K} (hμ1 : μ ≠ 1) (hscal : ∀ v, h * θ₀ v * h⁻¹ = θ₀ (μ • v)) {c : G}
    (hc : c ∈ lineN D a d) (hhc : Commute h c) : c ∈ lineN₀ D a d := by
  set P := Subgroup.centralizer ({h} : Set G) ⊓ lineN D a d with hP
  have hcP : c ∈ P := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hhc.eq.symm, hc⟩
  have hPN : P ≤ lineN D a d := inf_le_right
  have hconjP : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, ∀ c ∈ P, g * c * g⁻¹ ∈ P := by
    intro g hg c hc
    obtain ⟨hc1, hc2⟩ := Subgroup.mem_inf.1 hc
    refine Subgroup.mem_inf.2 ⟨?_, M.conj_N g hg c hc2⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc1 ⊢
    have h1 : Commute h c := hc1.symm
    exact (((hhX g hg).mul_right h1).mul_right (hhX _ (Subgroup.inv_mem _ hg))).eq.symm
  have hPT : ∀ t ∈ P, t ∈ rootGroup D a ⊔ rootGroup D d → t = 1 := by
    intro t ht htT
    obtain ⟨v, rfl⟩ := (M.range₀ t).1 htT
    have h1 := (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 ht).1)
    have h2 : θ₀ (μ • v) = θ₀ v := by rw [← hscal, ← h1, mul_inv_cancel_right]
    have h3 := M.nat₀.injective h2
    have hv : v = 0 := by
      have h4 : (μ - 1) • v = 0 := by rw [sub_smul, one_smul, h3, sub_self]
      exact (smul_eq_zero.1 h4).resolve_left (sub_ne_zero.2 hμ1)
    rw [hv, M.θ₀_zero]
  have ha := C.le_Na_of_forall_mem hPN (fun c hc => hconjP x C.x_mem_X c hc) hPT hcP
  have hPN' : P ≤ lineN D d a := by rw [lineN_comm]; exact hPN
  have hd := C.symm.le_Na_of_forall_mem hPN' (fun c hc => hconjP y C.y_mem_X c hc)
    (fun t ht htT => hPT t ht (by rwa [sup_comm] at htT)) hcP
  exact mem_lineN₀_of_mem ha hd

theorem eq_one_of_trivial (CT : ThinGateCounter G D) {h : G} (hp : (orderOf h).Prime)
    (hp2 : orderOf h ≠ 2) (hΩ : ¬ orderOf h ∣ (oneOmega D a).ncard)
    (hhX : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute h g)
    (hhT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute h t)
    (hhN₀ : ∀ m ∈ lineN₀ D a d, h * m * h⁻¹ ∈ lineN₀ D a d)
    (hV : ∀ v, (θ₁ v)⁻¹ * (h * θ₁ v * h⁻¹) ∈ lineN₀ D a d) : h = 1 := by
  classical
  have := C.finite
  have hD := C.root
  have hha : Commute h a := hhT a (left_mem_line C.ha)
  have hxM : rootGroup D x ≤ nCore D a :=
    le_sup_right.trans (C.setting.sup_rootGroup_le_nCore C.ha C.hx C.hax)
  have hfix : ∀ n ∈ lineN D a d, ∃ c : G, n⁻¹ * c ∈ lineN₀ D a d ∧ h * c * h⁻¹ = c := by
    intro n hn
    obtain ⟨v, hv⟩ := M.nat₁.exists_eq n hn
    refine exists_fixed_mem_coset (isPGroup_lineN₀ a d) hp hp2 hhN₀ ?_
    have e : n⁻¹ * (h * n * h⁻¹) = ((θ₁ v)⁻¹ * n)⁻¹ * ((θ₁ v)⁻¹ * (h * θ₁ v * h⁻¹)) *
        (h * ((θ₁ v)⁻¹ * n) * h⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) (hV v)) (hhN₀ _ hv)
  have hxconj : ∀ n ∈ lineN D a d, ∀ u ∈ rootGroup D x, Commute h (n * u * n⁻¹) := by
    intro n hn u hu
    obtain ⟨c, hc, hhc⟩ := hfix n hn
    have hcc : Commute h c := by
      show h * c = c * h
      calc h * c = h * c * h⁻¹ * h := by group
        _ = c * h := by rw [hhc]
    have hmM : (n⁻¹ * c)⁻¹ ∈ nCore D a :=
      (Subgroup.mem_inf.1 (Subgroup.inv_mem _ hc)).1
    have hcomm : (n⁻¹ * c)⁻¹ * u * (n⁻¹ * c)⁻¹⁻¹ * u⁻¹ ∈ rootGroup D a :=
      nCoreCommutatorInRoot_of_hyp C.setting.hyp C.setting.closure a C.ha _ hmM u (hxM hu)
    have h1 : Commute h ((n⁻¹ * c)⁻¹ * u * (n⁻¹ * c)) := by
      have := (hhT _ (Subgroup.mem_sup_left hcomm)).mul_right (hhX u (Subgroup.mem_sup_left hu))
      rwa [show (n⁻¹ * c)⁻¹ * u * (n⁻¹ * c)⁻¹⁻¹ * u⁻¹ * u = (n⁻¹ * c)⁻¹ * u * (n⁻¹ * c) by
        group] at this
    rw [show n * u * n⁻¹ = c * ((n⁻¹ * c)⁻¹ * u * (n⁻¹ * c)) * c⁻¹ by group]
    exact (hcc.mul_right h1).mul_right hcc.inv_right
  have hline : ∀ L ∈ rootLines D a, ∀ t ∈ L, Commute h t := by
    rintro L ⟨b, hb, hab, habD, hbT, rfl⟩ t ht
    by_cases hbL : b ∈ rootGroup D a ⊔ rootGroup D d
    · rw [C.setting.sup_rootGroup_eq_of_mem_sup C.ha hb C.hd hab hbT C.had C.hadD C.hdT hbL]
        at ht
      exact hhT t ht
    · obtain ⟨⟨k, hk, hkL⟩, -⟩ := rootLinesRegularStep G D C.setting a C.ha d C.hd C.had C.hadD
        C.hdT x C.hx C.hax C.haxD C.hxT b hb hab habD hbL
      have hkN : k ∈ lineN D a d := Subgroup.mem_sup_right hk
      have hle : rootGroup D a ⊔ rootGroup D x ≤
          (Subgroup.centralizer ({h} : Set G)).comap (MulAut.conj k).toMonoidHom := by
        refine sup_le (fun α hα => ?_) (fun u hu => ?_) <;>
          rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] <;>
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        · rw [(C.commute_of_mem_lineN hkN (Subgroup.mem_sup_left hα)).eq, mul_inv_cancel_right]
          exact (hhT α (Subgroup.mem_sup_left hα)).eq.symm
        · exact (hxconj k hkN u hu).eq.symm
      rw [← hkL] at ht
      obtain ⟨t', ht', rfl⟩ := ht
      have := hle ht'
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at this
      exact this.symm
  have hCa : ∀ f ∈ D, Commute a f → Commute h f := by
    intro f hf haf
    by_cases hfT : f ∈ rootSet D a
    · exact hhT f (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a hfT))
    · rcases C.setting.mem_rootSet_or_collinear C.ha hf haf.symm with h' | ⟨h1, h2⟩
      · exact absurd h' hfT
      · exact hline _ ⟨f, hf, h1, h2, hfT, rfl⟩ f (right_mem_line hf)
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have : Fact (orderOf h).Prime := ⟨hp⟩
  have hiter : ∀ (k : ℕ) (B : Subgroup G),
      (fun B : Subgroup G => B.map (MulAut.conj h).toMonoidHom)^[k] B =
        B.map (MulAut.conj (h ^ k)).toMonoidHom := by
    intro k
    induction k with
    | zero => intro B; rw [Function.iterate_zero_apply, pow_zero, RankOne.map_conj_one]
    | succ k ih =>
      intro B
      rw [Function.iterate_succ_apply', ih, pow_succ', RankOne.map_conj_mul]
  obtain ⟨B, hB, hBfix⟩ := RootDegen.exists_fixed_of_prime (S := oneOmega D a)
    (fun B hB => RootMany.map_conj_mem_oneOmega CT hha hB)
    (fun B _ => by rw [hiter, pow_orderOf_eq_one, RankOne.map_conj_one])
    (by rwa [Nat.card_coe_set_eq])
  obtain ⟨u, hu, rfl, hau, hoddau, hu1⟩ := hB
  have huA : u ∈ rootGroup D u := rootSet_subset_rootGroup D u (mem_rootSet_self hu)
  have hhuA : h * u * h⁻¹ ∈ rootGroup D u := by
    have : h * u * h⁻¹ ∈ (rootGroup D u).map (MulAut.conj h).toMonoidHom := ⟨u, huA, rfl⟩
    rwa [hBfix] at this
  have hhuT : h * u * h⁻¹ ∈ rootSet D u :=
    mem_rootSet_of_mem_rootGroup_of_ne_one hD C.setting.closure hu hhuA (fun h' => hD.ne_one hu (by
      have := congrArg (fun w => h⁻¹ * w * h) h'
      simpa [mul_assoc] using this))
  have hga' : ∀ a' ∈ rootSet D a, Commute h a' := fun a' h' =>
    hhT a' (Subgroup.mem_sup_left (rootSet_subset_rootGroup D a h'))
  have hhu : Commute h u :=
    commute_of_conj_mem_rootSet_of_centralizes' C.setting.hyp C.setting.closure
      C.setting.special C.ha hu hau hoddau hu1 hga' hhuT huA
  have htop := RootClosure.closure_insert_centralizer_eq_top C.setting.hyp C.setting.conn C.ha hu
    hau hoddau
  have hcen : h ∈ Subgroup.center G := by
    have hle : Subgroup.closure (insert u {f | f ∈ D ∧ Commute a f}) ≤
        Subgroup.centralizer ({h} : Set G) := by
      rw [Subgroup.closure_le]
      rintro f (rfl | ⟨hf, haf⟩) <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      · exact hhu.eq.symm
      · exact (hCa f hf haf).eq.symm
    rw [htop] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
  rw [C.setting.hyp.center_eq_bot, Subgroup.mem_bot] at hcen
  exact hcen

end ModConf

end RootOne

end CFSG.Timmesfeld.Bridge
