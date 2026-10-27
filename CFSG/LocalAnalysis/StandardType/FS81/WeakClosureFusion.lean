module

public import CFSG.LocalAnalysis.StandardType.FS81.Pieces
public import CFSG.LocalAnalysis.StandardType.FS81.Realized
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAb
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbE7
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.StandardType.FS81.RowFacts
public import CFSG.LocalAnalysis.StandardType.FS81.SplitE

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

theorem fs81Fus_sup_normal {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal) :
    ((K ⊔ (Subgroup.centralizer ({b₀} : Set G) ⊓ Subgroup.centralizer (K : Set G))).subgroupOf
      (Subgroup.centralizer ({b₀} : Set G))).Normal := by
  let C := Subgroup.centralizer ({b₀} : Set G)
  let D := C ⊓ Subgroup.centralizer (K : Set G)
  have hD_le_C : D ≤ C := inf_le_left
  have hD_normal_C : (D.subgroupOf C).Normal := by
    have hDc_eq : D.subgroupOf C = Subgroup.centralizer (K.subgroupOf C : Set C) := by
      ext x
      constructor
      · intro hx
        rw [Subgroup.mem_subgroupOf] at hx
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hx.2 (y : G) hy
      · intro hx
        rw [Subgroup.mem_centralizer_iff] at hx
        refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
        intro y hy
        have hyC : y ∈ C := hKC hy
        exact congrArg Subtype.val (hx ⟨y, hyC⟩ hy)
    rw [hDc_eq]
    exact Subgroup.normal_centralizer (H := K.subgroupOf C)
  rw [Subgroup.subgroupOf_sup hKC hD_le_C]
  have : (K.subgroupOf C).Normal := hKn
  have : (D.subgroupOf C).Normal := hD_normal_C
  exact Subgroup.sup_normal (K.subgroupOf C) (D.subgroupOf C)

theorem fs81Fus_exists_mul_zpow {G : Type} [Group G] [Finite G] {b₀ : G} {K : Subgroup G}
    (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    {x : G} (hxC : x ∈ Subgroup.centralizer ({b₀} : Set G)) (hx3 : x ^ 3 = 1) :
    ∃ k ∈ K, k ^ 3 = 1 ∧ ∃ i : ℤ, x = k * b₀ ^ i := by
  let C := Subgroup.centralizer ({b₀} : Set G)
  let D := C ⊓ Subgroup.centralizer (K : Set G)
  have hb₀_mem_C : b₀ ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  have hb₀_mem_CK : b₀ ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (Subgroup.mem_centralizer_iff.mp (hKC hk) b₀ (by simp)).symm
  have hb₀_mem_D : b₀ ∈ D := ⟨hb₀_mem_C, hb₀_mem_CK⟩
  have hKD_disjoint : K ⊓ D = ⊥ := fs81Sp_inf_eq_bot hKC hKz
  have hS : ((K ⊔ D).subgroupOf C).Normal := fs81Fus_sup_normal hKC hKn
  have hidx : ¬ 3 ∣ ((K ⊔ D).subgroupOf C).index := fs81Sp_no_three_index hKC hKn hOut
  have hxC3 : (⟨x, hxC⟩ : C) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxP : IsPGroup 3 (Subgroup.zpowers (⟨x, hxC⟩ : C)) :=
    (isElemAbelian_zpowers hxC3).isPGroup
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (p := 3) (G := C) hxP
  have hPle : (P : Subgroup C) ≤ (K ⊔ D).subgroupOf C := fs81Sp_sylow_le_normal hidx P
  have hxKD : x ∈ K ⊔ D := hPle (hP (Subgroup.mem_zpowers _))
  obtain ⟨k, hk, d, hd, hxkd⟩ := fs81Sp_mem_sup_of_commute fs81Sp_comm hxKD
  have hkd : Commute k d := fs81Sp_comm k hk d hd
  have h1 : k ^ 3 * d ^ 3 = 1 := by rw [← hkd.mul_pow, ← hxkd, hx3]
  have hk3 : k ^ 3 = 1 := by
    have hk3D : k ^ 3 ∈ D := by
      rw [eq_inv_of_mul_eq_one_left h1]
      exact D.inv_mem (D.pow_mem hd 3)
    have hmem : k ^ 3 ∈ K ⊓ D := ⟨K.pow_mem hk 3, hk3D⟩
    rw [hKD_disjoint] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hd3 : d ^ 3 = 1 := by
    rw [hk3, one_mul] at h1
    exact h1
  have hd_comm_b₀ : d * b₀ = b₀ * d :=
    (Subgroup.mem_centralizer_iff.mp hd.1 b₀ (by simp)).symm
  have hd_in_zp : d ∈ Subgroup.zpowers b₀ := by
    have hH_le_D : Subgroup.zpowers d ⊔ Subgroup.zpowers b₀ ≤ D := by
      apply sup_le
      · exact Subgroup.zpowers_le.mpr hd
      · exact Subgroup.zpowers_le.mpr hb₀_mem_D
    have hH_le_CK : Subgroup.zpowers d ⊔ Subgroup.zpowers b₀ ≤
        Subgroup.centralizer (K : Set G) :=
      hH_le_D.trans inf_le_right
    have hH_pgroup : IsPGroup 3 ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) := by
      have hd_elem : IsElemAbelian 3 (Subgroup.zpowers d) := isElemAbelian_zpowers hd3
      have hb0_elem : IsElemAbelian 3 (Subgroup.zpowers b₀) :=
        isElemAbelian_zpowers (by rw [← hb₀]; exact pow_orderOf_eq_one b₀)
      exact (hd_elem.sup_of_commute hb0_elem (by
        intro a ha b hb
        obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← hi, ← hj]
        exact ((show Commute d b₀ from hd_comm_b₀).zpow_left i).zpow_right j)).isPGroup
    have : IsCyclic ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) :=
      hA2 (Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) hH_le_CK hH_pgroup
    let dH : ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) :=
      ⟨d, Subgroup.mem_sup_left (Subgroup.mem_zpowers d)⟩
    let b₀H : ↥(Subgroup.zpowers d ⊔ Subgroup.zpowers b₀) :=
      ⟨b₀, Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)⟩
    have hd3H : dH ^ 3 = 1 := by
      apply Subtype.ext
      simp [dH, hd3]
    have hb₀_order_H : orderOf b₀H = 3 := by
      rw [← Subgroup.orderOf_coe b₀H]
      exact hb₀
    have hmem := fs81Sp_order3_unique (d := dH) (b₀ := b₀H) hb₀_order_H hd3H
    rw [Subgroup.mem_zpowers_iff] at hmem
    obtain ⟨j, hj⟩ := hmem
    rw [Subgroup.mem_zpowers_iff]
    use j
    have := congrArg Subtype.val hj
    simpa [dH, b₀H] using this
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hd_in_zp
  exact ⟨k, hk, hk3, i, by rw [hxkd, hi]⟩

theorem fs81Fus_card_sup_le {G : Type} [Group G] [Finite G] {H N : Subgroup G}
    (hcomm : ∀ a ∈ H, ∀ b ∈ N, a * b = b * a) :
    Nat.card ↥(H ⊔ N) ≤ Nat.card H * Nat.card N := by
  let f : ↥H × ↥N → ↥(H ⊔ N) := fun p =>
    ⟨(p.1 : G) * p.2, Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨x, hx⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := fs81Sp_mem_sup_of_commute hcomm hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  calc Nat.card ↥(H ⊔ N) ≤ Nat.card (↥H × ↥N) := Nat.card_le_card_of_surjective f hf
    _ = Nat.card H * Nat.card N := Nat.card_prod _ _

private theorem fs81Fus_zpow_comm {G : Type} [Group G] {b₀ y : G}
    (hy : y ∈ Subgroup.centralizer ({b₀} : Set G)) (i : ℤ) : y * b₀ ^ i = b₀ ^ i * y :=
  ((show Commute y b₀ from (Subgroup.mem_centralizer_iff.mp hy b₀ (by simp)).symm).zpow_right i).eq

theorem fs81Fus_exists_conj_eq {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    {n : ℕ} (hb₀ : orderOf b₀ = 3) (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hrank : ∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ n)
    (hconj : ∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ n →
      ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = E ⊓ K)
    {E' : Subgroup G} (hE'C : E' ≤ Subgroup.centralizer ({b₀} : Set G))
    (hE' : IsElemAbelian 3 E') (hcard : Nat.card E' = 3 ^ (n + 1)) :
    ∃ k ∈ K, E'.map (MulAut.conj k).toMonoidHom = E := by
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hb₀_mem_C : b₀ ∈ Subgroup.centralizer ({b₀} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
  have hcommC : ∀ a ∈ Subgroup.zpowers b₀, ∀ y ∈ Subgroup.centralizer ({b₀} : Set G),
      a * y = y * a := by
    intro a ha y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (fs81Fus_zpow_comm hy i).symm
  let F := Subgroup.zpowers b₀ ⊔ E'
  have hFC : F ≤ Subgroup.centralizer ({b₀} : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hb₀_mem_C) hE'C
  have hFel : IsElemAbelian 3 F :=
    (isElemAbelian_zpowers hb₀3).sup_of_commute hE' fun a ha y hy => hcommC a ha y (hE'C hy)
  let A' := F ⊓ K
  have hA'K : A' ≤ K := inf_le_right
  have hA'el : IsElemAbelian 3 A' := hFel.mono inf_le_left
  have hFeq : F = Subgroup.zpowers b₀ ⊔ A' := by
    apply le_antisymm
    · intro x hx
      obtain ⟨k, hk, -, i, rfl⟩ :=
        fs81Fus_exists_mul_zpow hb₀ hKC hKn hKz hOut hA2 (hFC hx) (hFel.2 _ hx)
      have hbi : b₀ ^ i ∈ F := F.zpow_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers b₀)) i
      have hkF : k ∈ F := by
        have hk' : k = k * b₀ ^ i * (b₀ ^ i)⁻¹ := by group
        rw [hk']
        exact F.mul_mem hx (F.inv_mem hbi)
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨hkF, hk⟩)
        (Subgroup.mem_sup_left (Subgroup.zpow_mem _ (Subgroup.mem_zpowers b₀) i))
    · exact sup_le le_sup_left inf_le_left
  have hcardF : Nat.card F ≤ 3 * Nat.card A' := by
    have h := fs81Fus_card_sup_le (H := Subgroup.zpowers b₀) (N := A')
      fun a ha y hy => hcommC a ha y (hFC hy.1)
    rw [Nat.card_zpowers, hb₀, ← hFeq] at h
    exact h
  have hE'F : E' ≤ F := le_sup_right
  have hcardE'F : Nat.card E' ≤ Nat.card F := Subgroup.card_le_of_le hE'F
  have h1 := hrank A' hA'K hA'el
  rw [hcard, pow_succ] at hcardE'F
  have hA'card : Nat.card A' = 3 ^ n := by omega
  have hE'eq : E' = F := Subgroup.eq_of_le_of_card_ge hE'F (by rw [hcard, pow_succ]; omega)
  obtain ⟨k, hk, hkA⟩ := hconj A' hA'K hA'el hA'card
  refine ⟨k, hk, ?_⟩
  have hkb : (MulAut.conj k).toMonoidHom b₀ = b₀ := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      show k * b₀ = b₀ * k from by simpa using fs81Fus_zpow_comm (hKC hk) 1, mul_inv_cancel_right]
  rw [hE'eq, hFeq, Subgroup.map_sup, hkA, MonoidHom.map_zpowers, hkb, hsup]

theorem card_realized_normalizer_le_of_localOrth {G : Type} [Group G] {b₀ : G} {n : ℕ}
    {B : Basis3 G (n + 1)} (h : LocalOrthI B b₀ ∨ LocalOrthII B b₀) :
    Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) ≤
      2 ^ (n + 1) * (n + 1).factorial := by
  rcases h with ⟨-, h | h⟩ | ⟨-, h | h | h⟩ <;> rw [h] <;> exact card_spSet_le _ _

theorem fs81Fus_card_realized_normalizer_le {G : Type} [Group G] {b₀ : G} {r : Row}
    {B : Basis3 G (r.n + 1)} (h : LocalData r B b₀) :
    Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) ≤
      2 ^ r.m * r.m.factorial := by
  cases r with
  | D6 => exact card_realized_normalizer_le_of_localOrth h
  | twD7 => exact card_realized_normalizer_le_of_localOrth h
  | E7 =>
    obtain ⟨hC, hN, -⟩ := h
    have hle : Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) ≤
        2 * 2903040 := by
      rcases hN with hN | hN
      · have h := (congrArg (fun s : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) => Nat.card ↥s) hN).trans
          hC
        exact h.le.trans (by norm_num)
      · exact le_of_eq hN
    refine hle.trans ?_
    show 2 * 2903040 ≤ 2 ^ 8 * Nat.factorial 8
    norm_num [Nat.factorial]

theorem fus42_of_facts {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G} {n : ℕ}
    {B : Basis3 G (n + 1)} (hb₀ : orderOf b₀ = 3)
    (hKC : K ≤ Subgroup.centralizer ({b₀} : Set G))
    (hKn : (K.subgroupOf (Subgroup.centralizer ({b₀} : Set G))).Normal)
    (hKz : Subgroup.center K = ⊥) (hOut : ¬ 3 ∣ Nat.card (Outer K))
    (hA2 : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (K : Set G) → IsPGroup 3 S → IsCyclic S)
    (hEmax : IsMaxElemAb3 (Subgroup.centralizer ({b₀} : Set G)) E)
    (hEcard : Nat.card E = 3 ^ (n + 1)) (hsup : Subgroup.zpowers b₀ ⊔ (E ⊓ K) = E)
    (hrank : ∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' ≤ 3 ^ n)
    (hconj : ∀ A' : Subgroup G, A' ≤ K → IsElemAbelian 3 A' → Nat.card A' = 3 ^ n →
      ∃ k ∈ K, A'.map (MulAut.conj k).toMonoidHom = E ⊓ K)
    (hspan : B.span = E)
    (hX : Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) <
      Nat.card ↥(ggAutomizer ⊤ E)) :
    Fus42 B b₀ := by
  have hc : ∀ g : G, g * b₀ * g⁻¹ ∈ E →
      ∃ x ∈ Subgroup.normalizer (E : Set G), g * b₀ * g⁻¹ = x * b₀ * x⁻¹ := by
    intro g hg
    have hE'C : E.map (MulAut.conj g⁻¹).toMonoidHom ≤ Subgroup.centralizer ({b₀} : Set G) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have hyb : y * (g * z * g⁻¹) = (g * z * g⁻¹) * y :=
        congrArg Subtype.val (hEmax.2.1.1.is_comm.comm ⟨y, hy⟩ ⟨_, hg⟩)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      calc z * (g⁻¹ * y * g) = g⁻¹ * ((g * z * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * z * g⁻¹)) * g := by rw [hyb]
        _ = g⁻¹ * y * g * z := by group
    have hE'el : IsElemAbelian 3 (E.map (MulAut.conj g⁻¹).toMonoidHom) := hEmax.2.1.map _
    have hE'card : Nat.card (E.map (MulAut.conj g⁻¹).toMonoidHom) = 3 ^ (n + 1) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hEcard]
    obtain ⟨k, hk, hkE⟩ :=
      fs81Fus_exists_conj_eq hb₀ hKC hKn hKz hOut hA2 hsup hrank hconj hE'C hE'el hE'card
    have hy : k * g⁻¹ ∈ Subgroup.normalizer (E : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hcomp : (↑(MulAut.conj (k * g⁻¹)) : G →* G) =
          (MulAut.conj k).toMonoidHom.comp (MulAut.conj g⁻¹).toMonoidHom := by
        ext z
        simp [MulAut.conj_apply, mul_assoc]
      rw [hcomp, ← Subgroup.map_map]
      exact hkE
    refine ⟨(k * g⁻¹)⁻¹, Subgroup.inv_mem _ hy, ?_⟩
    have hkb : k * b₀ = b₀ * k := by simpa using fs81Fus_zpow_comm (hKC hk) 1
    calc g * b₀ * g⁻¹ = g * k⁻¹ * (k * b₀) * g⁻¹ := by group
      _ = g * k⁻¹ * (b₀ * k) * g⁻¹ := by rw [hkb]
      _ = (k * g⁻¹)⁻¹ * b₀ * (k * g⁻¹)⁻¹⁻¹ := by group
  rw [Fus42, hspan]
  refine ⟨fun hle => ?_, hc⟩
  have hsub : B.realized ⊤ ⊆
      B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) := by
    rintro A ⟨g, -, hg⟩
    have hgN := B.mem_normalizer_of_acts hg
    rw [hspan] at hgN
    exact ⟨g, hle hgN, hg⟩
  have h1 := B.card_ggAutomizer_le ⊤
  rw [hspan] at h1
  have h2 : Nat.card ↥(B.realized ⊤) ≤
      Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) :=
    Nat.card_mono (Set.toFinite _) hsub
  exact absurd (lt_of_lt_of_le hX (h1.trans h2)) (lt_irrefl _)

theorem l1Fus42_of
    (hR : RowElemAb3) : L1Fus42 := by
  intro G _ _ b₀ K E r hStd B hAd hLoc
  obtain ⟨-, ⟨hA, hEmax, -, hEcard, -, hX⟩, hrow, -, hsup, hEKmax, hEKcard, -⟩ := hStd
  obtain ⟨hb₀, hKC, hKn, hKz, hKmark, hA2, -, -⟩ := hA
  obtain ⟨hspan, -, -⟩ := hAd
  have hOut := fs81_row_out_not_dvd_three hKmark hKz
  obtain ⟨hrank, hconj⟩ := hR G K (E ⊓ K) r hrow hKz inf_le_right hEKmax.2.1 hEKcard
  exact fus42_of_facts hb₀ hKC hKn hKz hOut hA2 hEmax hEcard hsup hrank hconj hspan
    (lt_of_le_of_lt (fs81Fus_card_realized_normalizer_le hLoc) hX)

theorem rowElemAb3_holds :
    RowElemAb3 := by
  intro G _ _ K A r hrow hZ hAK hA hAcard
  cases r with
  | D6 => exact rowElemAb3_D6 hrow hZ hAK hA hAcard
  | twD7 => exact rowElemAb3_twD7 hrow hZ hAK hA hAcard
  | E7 => exact rowElemAb3_E7 hrow hZ hAK hA hAcard

theorem l1Fus42_holds :
    L1Fus42 :=
  l1Fus42_of rowElemAb3_holds

end CFSG.StandardType.FrameRoute.FS81

end
