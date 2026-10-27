module

public import CFSG.Quasithin.Background.SmithD310UBeta
public import CFSG.Quasithin.Background.SmithD39TwoMult

public section

namespace CFSG.Quasithin.SmithD310U

open CFSG.Quasithin.Z391 CFSG.Quasithin.SmithD391 CFSG.Quasithin.SmithD39Two
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

section Elementary

theorem smul_mem_commOf {Γ : Type*} [Group Γ] {Q : Type*} [CommGroup Q]
    [MulDistribMulAction Γ Q] {E : Subgroup Γ} {S : Subgroup Q} {g : Γ}
    (hgE : ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hgS : ∀ s ∈ S, g • s ∈ S) :
    ∀ q ∈ XMod.commOf ↥E S, g • q ∈ XMod.commOf ↥E S := by
  intro q hq
  unfold XMod.commOf at hq
  induction hq using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨e, s, hs, rfl⟩ := hc
    have h1 : g • ((e • s) * s⁻¹) =
        ((⟨g * e * g⁻¹, hgE e e.2⟩ : ↥E) • (g • s)) * (g • s)⁻¹ := by
      rw [smul_mul', smul_inv', Subgroup.smul_def, Subgroup.smul_def]
      congr 1
      show g • (e : Γ) • s = (g * e * g⁻¹) • g • s
      rw [smul_smul, smul_smul, inv_mul_cancel_right]
    rw [h1]
    exact XMod.mem_commOf_of_mem _ (hgS s hs)
  | one => rw [smul_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [smul_mul']; exact mul_mem hx hy
  | inv x _ hx => rw [smul_inv']; exact inv_mem hx

theorem rk_eq_add_one_of_split {G : Type*} [Group G] [Finite G] {A B : Subgroup G}
    (hBA : B ≤ A) {a : G} (ha : a ∈ A) (haB : a ∉ B) (hsplit : ∀ x ∈ A, x ∈ B ∨ a⁻¹ * x ∈ B) :
    rk ↥A = rk ↥B + 1 := by
  have hlt : B < A := lt_of_le_of_ne hBA fun h => haB (h ▸ ha)
  have hcard : Nat.card ↥A ≤ 2 * Nat.card ↥B := by
    let f : ↥B ⊕ ↥B → ↥A := fun x => match x with
      | Sum.inl b => ⟨b, hBA b.2⟩
      | Sum.inr b => ⟨a * b, A.mul_mem ha (hBA b.2)⟩
    have hf : Function.Surjective f := by
      rintro ⟨x, hx⟩
      rcases hsplit x hx with h | h
      · exact ⟨Sum.inl ⟨x, h⟩, rfl⟩
      · refine ⟨Sum.inr ⟨a⁻¹ * x, h⟩, Subtype.ext ?_⟩
        show a * (a⁻¹ * x) = x
        group
    have := Nat.card_le_card_of_surjective f hf
    rw [Nat.card_sum] at this
    omega
  have hmul := Subgroup.relIndex_mul_card B A
  rw [inf_eq_left.mpr hBA] at hmul
  have h1 : B.relIndex A ≠ 1 := fun h => absurd (Subgroup.relIndex_eq_one.mp h) (not_le_of_gt hlt)
  have hpos : 0 < Nat.card ↥B := Nat.card_pos
  have h2 : B.relIndex A ≤ 2 := by
    by_contra h
    have : 3 * Nat.card ↥B ≤ B.relIndex A * Nat.card ↥B := Nat.mul_le_mul_right _ (by omega)
    omega
  have h0 : B.relIndex A ≠ 0 := by
    intro h
    rw [h, zero_mul] at hmul
    exact (Nat.card_pos (α := A)).ne' hmul.symm
  have h3 : B.relIndex A = 2 := by omega
  rw [h3] at hmul
  unfold rk
  rw [← hmul, padicValNat.mul two_ne_zero Nat.card_pos.ne', padicValNat_self]
  omega

theorem conj_eq_or_eq_inv {G : Type*} [Group G] [Finite G] {P : Subgroup G} (hP : IsCyclic ↥P)
    {y : G} (hyP : y ∈ P) (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) {x : G} (hxy : x * y * x⁻¹ ∈ P) :
    x * y * x⁻¹ = y ∨ x * y * x⁻¹ = y⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set z := x * y * x⁻¹ with hz
  have hy3' : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hz1 : z ≠ 1 := by
    intro h
    apply hy1
    have h2 : y = x⁻¹ * z * x := by rw [hz]; group
    rw [h2, h]
    group
  have hz3 : orderOf z = 3 := by
    refine orderOf_eq_prime ?_ hz1
    rw [hz, conj_pow, hy3]
    group
  have hcard : Nat.card (Subgroup.zpowers (⟨y, hyP⟩ : ↥P)) =
      Nat.card (Subgroup.zpowers (⟨z, hxy⟩ : ↥P)) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hy3', hz3]
  have heq := (IsCyclic.subgroup_eq_iff_card_eq (H := Subgroup.zpowers (⟨y, hyP⟩ : ↥P))
    (K := Subgroup.zpowers (⟨z, hxy⟩ : ↥P))).2 hcard
  have hzmem : (⟨z, hxy⟩ : ↥P) ∈ Subgroup.zpowers (⟨y, hyP⟩ : ↥P) := by
    rw [heq]; exact Subgroup.mem_zpowers _
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hzmem
  have hn' : y ^ n = z := by
    have := congrArg Subtype.val hn
    simpa using this
  have hmod : y ^ (n % 3) = z := by
    have h := zpow_mod_orderOf y n
    rw [hy3'] at h
    rw [← hn']
    exact_mod_cast h
  have h0 : 0 ≤ n % 3 := Int.emod_nonneg n (by norm_num)
  have h3 : n % 3 < 3 := Int.emod_lt_of_pos n (by norm_num)
  rcases (show n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 by omega) with h | h | h
  · rw [h, zpow_zero] at hmod
    exact absurd hmod.symm hz1
  · rw [h, zpow_one] at hmod
    exact Or.inl hmod.symm
  · right
    rw [← hmod, h]
    have : y ^ (2 : ℤ) * y = 1 := by
      rw [← zpow_add_one]
      norm_cast
    exact (inv_eq_of_mul_eq_one_left this).symm

private theorem subgroupOf_isSubnormal_of_open {X : Type*} [Group X] {A B : Subgroup X}
    (h : CFSG.Open.IsSubnormal A B) : (A.subgroupOf B).IsSubnormal :=
  h.subgroupOf

theorem commute_of_mem_cComp {G : Type*} [Group G] [Finite G] {M K K' : Subgroup G}
    (hK : K ∈ cComp M) (hKq : CFSG.IsQuasisimple ↥K) (hK' : K' ∈ cComp M)
    (hK'q : CFSG.IsQuasisimple ↥K') (hne : K ≠ K') : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
  have hKM := le_of_mem_cComp hK
  have hK'M := le_of_mem_cComp hK'
  have hc : ∀ {J : Subgroup G}, J ∈ cComp M → CFSG.IsQuasisimple ↥J →
      CFSG.IsComponent (J.subgroupOf M) := fun {J} hJ hJq =>
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_of_mem_cComp hJ)).symm hJq,
      subgroupOf_isSubnormal_of_open (subnormal_of_mem_cComp hJ)⟩
  rcases CFSG.LocalCores.distinct_components_commute (hc hK hKq) (hc hK' hK'q) with h | h
  · exfalso
    apply hne
    rw [← Subgroup.map_subgroupOf_eq_of_le hKM, ← Subgroup.map_subgroupOf_eq_of_le hK'M, h]
  · intro x hx y hy
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h
      (show (⟨x, hKM hx⟩ : ↥M) ∈ K.subgroupOf M from hx)
    have h2 := (Subgroup.mem_centralizer_iff.1 h1) ⟨y, hK'M hy⟩ hy
    exact (congrArg Subtype.val h2).symm

theorem map_conj_mem_cComp {G : Type*} [Group G] {M K : Subgroup G} (hK : K ∈ cComp M)
    {m : G} (hm : m ∈ M) : K.map (MulAut.conj m).toMonoidHom ∈ cComp M := by
  have h := cComp_map_mulEquiv (MulAut.conj m) hK
  have hM : M.map (MulAut.conj m).toMonoidHom = M := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact M.mul_mem (M.mul_mem hm hz) (M.inv_mem hm)
    · intro hx
      refine ⟨m⁻¹ * x * m, M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  rwa [hM] at h

theorem closure_odd_eq_of_perfect {G : Type*} [Group G] [Finite G] {K : Subgroup G}
    (hK : ⁅K, K⁆ = K) : Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} = K := by
  classical
  set N := Subgroup.closure {x | x ∈ K ∧ Odd (orderOf x)} with hNdef
  have hNK : N ≤ K := (Subgroup.closure_le K).2 fun x hx => hx.1
  refine le_antisymm hNK ?_
  set N' : Subgroup ↥K := N.subgroupOf K with hN'
  have hconj : ∀ k ∈ K, ∀ n ∈ N, k * n * k⁻¹ ∈ N := by
    intro k hkK n hn
    induction hn using Subgroup.closure_induction with
    | mem x hx =>
      refine Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hkK hx.1) (K.inv_mem hkK), ?_⟩
      have := orderOf_injective (MulAut.conj k).toMonoidHom (MulAut.conj k).injective x
      have e : (MulAut.conj k).toMonoidHom x = k * x * k⁻¹ := rfl
      rw [e] at this
      rw [this]
      exact hx.2
    | one => simp
    | mul x y _ _ hx hy =>
      have : k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) := by group
      rw [this]
      exact N.mul_mem hx hy
    | inv x _ hx =>
      have : k * x⁻¹ * k⁻¹ = (k * x * k⁻¹)⁻¹ := by group
      rw [this]
      exact N.inv_mem hx
  have hN'n : N'.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hconj k k.2 n hn
  have h2 : IsPGroup 2 (↥K ⧸ N') := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k =>
      obtain ⟨e, d, hd, hed⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos k).ne'
      refine ⟨e, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      refine Subgroup.subset_closure ⟨K.pow_mem k.2 _, ?_⟩
      have h1 : orderOf ((k : G) ^ 2 ^ e) = d := by
        rw [← Subgroup.orderOf_coe] at hed
        rw [orderOf_pow_of_dvd (by positivity) (by rw [hed]; exact Dvd.intro d rfl), hed]
        simp [Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ e)]
      rw [Subgroup.coe_pow, h1]
      exact hd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf : Group.IsPerfect (↥K ⧸ N') := by
    have : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hK
    exact Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N') (QuotientGroup.mk'_surjective _)
  have hsub : Subsingleton (↥K ⧸ N') := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    exact Group.IsPerfect.not_isNilpotent (↥K ⧸ N') h2.isNilpotent
  intro k hk
  have : (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : ↥K ⧸ N') = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at this
  exact this

theorem commSub_commSub_eq {W : Type} [CommGroup W] {K : Subgroup (MulAut W)} (hperf : ⁅K, K⁆ = K)
    (D : Subgroup W) : commSub (commSub D K) K = commSub D K := by
  have hU : ∀ x ∈ K, ∀ w ∈ commSub D K, x w ∈ commSub D K := by
    intro x hx w hw
    unfold commSub at hw ⊢
    induction hw using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨y, hy, v, hv, rfl⟩ := hc
      have e : x (y v * v⁻¹) = ((x * y) v * v⁻¹) * (x v * v⁻¹)⁻¹ := by
        simp only [map_mul, map_inv, MulAut.mul_apply]
        group
      rw [e]
      exact mul_mem (Subgroup.subset_closure ⟨x * y, K.mul_mem hx hy, v, hv, rfl⟩)
        (inv_mem (Subgroup.subset_closure ⟨x, hx, v, hv, rfl⟩))
    | one => rw [map_one]; exact one_mem _
    | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb
    | inv a _ ha => rw [map_inv]; exact inv_mem ha
  apply le_antisymm (commSub_le_of_invariant hU)
  set U' := commSub (commSub D K) K with hU'
  rw [commSub, Subgroup.closure_le]
  rintro _ ⟨x, hx, v, hvD, rfl⟩
  let f : ↥K →* W ⧸ U' :=
    { toFun := fun l => QuotientGroup.mk ((l : MulAut W) v * v⁻¹)
      map_one' := by simp
      map_mul' := fun l₁ l₂ => by
        have hw : (l₂ : MulAut W) v * v⁻¹ ∈ commSub D K :=
          Subgroup.subset_closure ⟨l₂, l₂.2, v, hvD, rfl⟩
        have h1 : (l₁ : MulAut W) ((l₂ : MulAut W) v * v⁻¹) * ((l₂ : MulAut W) v * v⁻¹)⁻¹ ∈ U' :=
          Subgroup.subset_closure ⟨l₁, l₁.2, _, hw, rfl⟩
        show (QuotientGroup.mk (((l₁ * l₂ : ↥K) : MulAut W) v * v⁻¹) : W ⧸ U') = _
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
        have e : (((l₁ * l₂ : ↥K) : MulAut W) v * v⁻¹)⁻¹ *
            ((l₁ : MulAut W) v * v⁻¹ * ((l₂ : MulAut W) v * v⁻¹)) =
            ((l₁ : MulAut W) ((l₂ : MulAut W) v * v⁻¹) * ((l₂ : MulAut W) v * v⁻¹)⁻¹)⁻¹ := by
          simp only [Subgroup.coe_mul, MulAut.mul_apply, map_mul, map_inv]
          cgroup
        rw [e]
        exact U'.inv_mem h1 }
  have hker : commutator ↥K ≤ f.ker := Abelianization.commutator_subset_ker f
  have hperf' : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hperf
  have h1 : (⟨x, hx⟩ : ↥K) ∈ f.ker := hker (by rw [hperf'.commutator_eq_top]; trivial)
  exact (QuotientGroup.eq_one_iff _).1 h1

theorem exists_chief_section_le {W : Type} [CommGroup W] [Finite W] {G K : Subgroup (MulAut W)}
    (hperf : ⁅K, K⁆ = K) {C D : Subgroup W} (hCD : C ≤ D) (hGC : G ≤ stabSub C)
    (hGD : G ≤ stabSub D) (hnt : ¬ commSub D K ≤ C) :
    ∃ U X : Subgroup W, C ≤ U ∧ U ≤ X ∧ X ≤ D ∧ G ≤ stabSub U ∧ G ≤ stabSub X ∧
      ¬ commSub X K ≤ U ∧
      ∀ J : Subgroup W, G ≤ stabSub J → U ≤ J → J ≤ X → J = U ∨ J = X := by
  classical
  let 𝒴 : Set (Subgroup W) := {J | G ≤ stabSub J ∧ C ≤ J ∧ J ≤ D ∧ ¬ commSub D K ≤ J}
  have h𝒴 : 𝒴.Nonempty := ⟨C, hGC, le_rfl, hCD, hnt⟩
  obtain ⟨U, hU, hUmax⟩ := Set.exists_max_image 𝒴 (fun J => Nat.card J) (Set.toFinite 𝒴) h𝒴
  let 𝒲 : Set (Subgroup W) := {J | G ≤ stabSub J ∧ U ≤ J ∧ J ≤ D ∧ ¬ commSub J K ≤ U}
  have h𝒲 : 𝒲.Nonempty := ⟨D, hGD, hU.2.2.1, le_rfl, hU.2.2.2⟩
  obtain ⟨X, hX, hXmin⟩ := Set.exists_min_image 𝒲 (fun J => Nat.card J) (Set.toFinite 𝒲) h𝒲
  refine ⟨U, X, hU.2.1, hX.2.1, hX.2.2.1, hU.1, hX.1, hX.2.2.2, ?_⟩
  intro J hGJ hUJ hJX
  by_cases hJX' : J = X
  · exact Or.inr hJX'
  · left
    have h1 : commSub J K ≤ U := by
      by_contra hcon
      have hmem : J ∈ 𝒲 := ⟨hGJ, hUJ, hJX.trans hX.2.2.1, hcon⟩
      exact hJX' (Subgroup.eq_of_le_of_card_ge hJX (hXmin J hmem))
    by_contra hne
    have hlt : U < J := lt_of_le_of_ne hUJ (Ne.symm hne)
    have hnotmem : J ∉ 𝒴 := fun hmem =>
      hlt.ne (Subgroup.eq_of_le_of_card_ge hUJ (hUmax J hmem))
    have hUJ' : commSub D K ≤ J := by
      by_contra hcon
      exact hnotmem ⟨hGJ, hU.2.1.trans hUJ, hJX.trans hX.2.2.1, hcon⟩
    apply hU.2.2.2
    calc commSub D K = commSub (commSub D K) K := (commSub_commSub_eq hperf D).symm
      _ ≤ commSub J K := commSub_mono hUJ' le_rfl
      _ ≤ U := h1

private theorem rk_map_add {G H : Type*} [Group G] [Group H] [Finite G] [Finite H] (K : Subgroup G)
    (f : G →* H) : rk ↥(K.map f) + rk ↥(K ⊓ f.ker) = rk ↥K := by
  have h1 := B1More.card_map_mul_card_inf_ker K f
  unfold rk
  rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h1]

theorem rkIdx_fixV_autSec_le_nB {W : Type} [CommGroup W] [Finite W] {M : Subgroup (MulAut W)}
    {Q : Type*} [CommGroup Q] [Finite Q] [MulDistribMulAction ↥M Q] (π : W →* Q)
    (hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w)) (A₀ : Subgroup ↥M)
    {X U : Subgroup W} (hUX : U ≤ X) (hker : π.ker ≤ U) :
    rkIdx (fixV (autSec (A₀.map M.subtype) X U)) ≤ Z391.nB A₀ (X.map π) := by
  classical
  set A : Subgroup (MulAut W) := A₀.map M.subtype with hA
  set F := XMod.fixed ↥A₀ (⊤ : Subgroup Q) with hF
  set J : Subgroup W := X ⊓ F.comap π with hJ
  set ρ : ↥X →* Sec X U := QuotientGroup.mk' (U.subgroupOf X) with hρ
  set J' : Subgroup ↥X := J.subgroupOf X with hJ'
  have himg : J'.map ρ ≤ fixV (autSec A X U) := by
    rintro _ ⟨v, hv, rfl⟩
    show (QuotientGroup.mk v : Sec X U) ∈ fixV (autQuot (autSub A X) (U.subgroupOf X))
    rw [mk_mem_fixV_autQuot]
    intro g hg _
    obtain ⟨g', hg'A, rfl⟩ := mem_autSub.mp hg
    obtain ⟨a, ha, hga⟩ := Subgroup.mem_map.mp hg'A
    rw [Subgroup.mem_subgroupOf]
    have hvJ : (v : W) ∈ J := hv
    have h1 : a • π v = π v := (XMod.mem_fixed.1 hvJ.2).2 ⟨a, ha⟩
    change (a : ↥M) • π v = π v at h1
    rw [hπM] at h1
    have h2 : (g'.1 : MulAut W) = (a : MulAut W) := hga.symm
    apply hker
    rw [MonoidHom.mem_ker]
    have h3 : (((resHom X g' v * v⁻¹ : ↥X)) : W) = (a : MulAut W) (v : W) * (v : W)⁻¹ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, ← h2]
      rfl
    rw [h3, map_mul, map_inv, h1, mul_inv_cancel]
  have hkerρ : J' ⊓ ρ.ker = (J ⊓ U).subgroupOf X := by
    ext v
    simp only [hρ, hJ', Subgroup.mem_inf, Subgroup.mem_subgroupOf, QuotientGroup.ker_mk']
  have e1 : rk ↥(J'.map ρ) + rk ↥(J' ⊓ ρ.ker) = rk ↥J' := rk_map_add J' ρ
  have e1' : rk ↥J' = rk ↥J := by
    unfold rk
    rw [hJ', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : J ≤ X)).toEquiv]
  have e1'' : rk ↥(J' ⊓ ρ.ker) = rk ↥(J ⊓ U) := by
    unfold rk
    rw [hkerρ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hUX)).toEquiv]
  have e2 : rk (Sec X U) + rk ↥U = rk ↥X := by
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', card_sec_mul hUX]
  have e3 : rk ↥(fixV (autSec A X U)) + rkIdx (fixV (autSec A X U)) = rk (Sec X U) :=
    rk_add_rkIdx (fixV (autSec A X U))
  have e4 : rk ↥(J'.map ρ) ≤ rk ↥(fixV (autSec A X U)) := rk_mono himg
  have hmapJ : X.map π ⊓ F = J.map π := by
    apply le_antisymm
    · rintro _ ⟨⟨x, hx, rfl⟩, hxF⟩
      exact ⟨x, ⟨hx, hxF⟩, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx.1, rfl⟩, hx.2⟩
  have e5 : rk ↥(X.map π) + rk ↥(X ⊓ π.ker) = rk ↥X := rk_map_add X π
  have hJK : J ⊓ π.ker = X ⊓ π.ker := by
    ext w
    simp only [hJ, Subgroup.mem_inf, Subgroup.mem_comap, MonoidHom.mem_ker]
    constructor
    · rintro ⟨⟨hx, -⟩, hk⟩
      exact ⟨hx, hk⟩
    · rintro ⟨hx, hk⟩
      refine ⟨⟨hx, ?_⟩, hk⟩
      rw [hk]
      exact F.one_mem
  have e6 : rk ↥(J.map π) + rk ↥(X ⊓ π.ker) = rk ↥J := by
    rw [← hJK]
    exact rk_map_add J π
  have e7 : rk ↥(J ⊓ U) ≤ rk ↥U := rk_mono inf_le_right
  have e8 : rk ↥J ≤ rk ↥X := rk_mono inf_le_left
  have e9 : Z391.nB A₀ (X.map π) = rk ↥(X.map π) - rk ↥(J.map π) := by
    unfold Z391.nB
    rw [hmapJ]
  rw [e9]
  omega

theorem isQuotientOfSQTKTC_of_le {G : Type*} [Group G] {M H : Subgroup G}
    (hMq : IsQuotientOfSQTKTC ↥M) (hHM : H ≤ M) : IsQuotientOfSQTKTC ↥H := by
  obtain ⟨S, _, _, hSQT, hSK, φ, hφ⟩ := hMq
  refine ⟨↥((H.subgroupOf M).comap φ), inferInstance, inferInstance, fun q hq hq2 => ?_,
    hSK.subgroup _, ?_⟩
  · exact (CFSG.SectionRank.pRank_top_le_of_injective hq.one_lt _
      ((H.subgroupOf M).comap φ).subtype_injective).trans (hSQT q hq hq2)
  · refine ⟨(Subgroup.subgroupOfEquivOfLe hHM).toMonoidHom.comp
      (φ.subgroupComap (H.subgroupOf M)), fun g => ?_⟩
    obtain ⟨h, hh⟩ := hφ ⟨(g : G), hHM g.2⟩
    have hmem : h ∈ (H.subgroupOf M).comap φ := by
      rw [Subgroup.mem_comap, hh]
      exact g.2
    refine ⟨⟨h, hmem⟩, Subtype.ext ?_⟩
    show ((φ h : ↥M) : G) = g
    rw [hh]

section Sections

variable {W : Type} [CommGroup W]

theorem autSec_eq_map {G L : Subgroup (MulAut W)} {X U : Subgroup W} (hGX : G ≤ stabSub X)
    (hGU : G ≤ stabSub U) (hLG : L ≤ G) :
    autSec L X U = (L.subgroupOf G).map (B5.secHom G hGX hGU) :=
  (B5.map_secHom_eq_autSec G hGX hGU hLG).symm

theorem commOf_autSec_eq_top {L : Subgroup (MulAut W)} {X U : Subgroup W}
    (hLX : L ≤ stabSub X) (hLU : L ≤ stabSub U) (hcomm : X ≤ commSub X L ⊔ U) :
    XMod.commOf ↥(autSec L X U) (⊤ : Subgroup (Sec X U)) = ⊤ := by
  set φ := B5.secHom L hLX hLU with hφ
  have hφL : ∀ l : ↥L, φ l ∈ autSec L X U := fun l => by
    rw [← B5.range_secHom L hLX hLU]
    exact ⟨l, rfl⟩
  have hcX : commSub X L ≤ X :=
    commSub_le_of_invariant fun x hx w hw => (hLX hx w).2 hw
  have key : ∀ c (hc : c ∈ commSub X L), (QuotientGroup.mk ⟨c, hcX hc⟩ : Sec X U) ∈
      XMod.commOf ↥(autSec L X U) (⊤ : Subgroup (Sec X U)) := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨l, hl, x, hx, rfl⟩ := hc
      have h1 : (QuotientGroup.mk ⟨l x * x⁻¹, hcX (Subgroup.subset_closure ⟨l, hl, x, hx, rfl⟩)⟩ :
          Sec X U) = ((⟨φ ⟨l, hl⟩, hφL ⟨l, hl⟩⟩ : ↥(autSec L X U)) •
            (QuotientGroup.mk ⟨x, hx⟩ : Sec X U)) * (QuotientGroup.mk ⟨x, hx⟩ : Sec X U)⁻¹ := by
        rw [Subgroup.smul_def]
        show _ = φ ⟨l, hl⟩ (QuotientGroup.mk ⟨x, hx⟩) * _
        rw [hφ, B5.secHom_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
        rfl
      rw [h1]
      exact XMod.mem_commOf_of_mem _ trivial
    | one => exact one_mem _
    | mul a b ha hb iha ihb =>
      have e : (QuotientGroup.mk ⟨a * b, hcX (mul_mem ha hb)⟩ : Sec X U) =
          QuotientGroup.mk ⟨a, hcX ha⟩ * QuotientGroup.mk ⟨b, hcX hb⟩ := rfl
      rw [e]
      exact mul_mem iha ihb
    | inv a ha iha =>
      have e : (QuotientGroup.mk ⟨a⁻¹, hcX (inv_mem ha)⟩ : Sec X U) =
          (QuotientGroup.mk ⟨a, hcX ha⟩)⁻¹ := rfl
      rw [e]
      exact inv_mem iha
  refine eq_top_iff.2 fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨c, hc, u, hu, hcu⟩ := Subgroup.mem_sup.1 (hcomm x.2)
    have e : (QuotientGroup.mk x : Sec X U) = QuotientGroup.mk ⟨c, hcX hc⟩ := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have : (x : W) = c * u := hcu.symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, this, mul_inv_rev, inv_mul_cancel_right]
      exact U.inv_mem hu
    rw [e]
    exact key c hc

theorem exists_three_copies_sec [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {L H : Subgroup (MulAut W)} {X U : Subgroup W} (hUX : U < X) (hLX : L ≤ stabSub X)
    (hLU : L ≤ stabSub U) (hHX : H ≤ stabSub X) (hHU : H ≤ stabSub U)
    (hLH : ∀ l ∈ L, ∀ h ∈ H, l * h = h * l) (hLq : CFSG.IsQuasisimple ↥L)
    (hirr : ∀ J : Subgroup W, L ⊔ H ≤ stabSub J → U ≤ J → J ≤ X → J = U ∨ J = X)
    (hcomm : X ≤ commSub X L ⊔ U) {g : MulAut W} (hgL : g ∈ L) (hg4 : g ^ 4 = 1)
    (hg2 : ∃ h ∈ L, g ^ 2 * h ≠ h * g ^ 2) :
    ∃ Y₁ : Subgroup (Sec X U), XMod.IsIrr ↥(autSec H X U) Y₁ ∧
      (∀ P : Subgroup (MulAut (Sec X U)), P ≤ autSec H X U →
        3 * Z391.nB P Y₁ ≤ Z391.nB P (⊤ : Subgroup (Sec X U))) ∧
      (∀ p ∈ autSec H X U, (∀ y ∈ Y₁, p • y = y) → ∀ r : Sec X U, p • r = r) := by
  have hQ : ∀ q : Sec X U, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hW (x : W))
      rw [this, QuotientGroup.mk_one]
  set G := L ⊔ H with hGdef
  have hGX : G ≤ stabSub X := sup_le hLX hHX
  have hGU : G ≤ stabSub U := sup_le hLU hHU
  set φ := B5.secHom G hGX hGU with hφ
  have hautL := autSec_eq_map hGX hGU (le_sup_left : L ≤ G)
  have hautH := autSec_eq_map hGX hGU (le_sup_right : H ≤ G)
  have hLH' : ∀ l ∈ autSec L X U, ∀ h ∈ autSec H X U, l * h = h * l := by
    intro l hl h hh
    rw [hautL] at hl
    rw [hautH] at hh
    obtain ⟨l', hl', rfl⟩ := hl
    obtain ⟨h', hh', rfl⟩ := hh
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hLH _ hl' _ hh')
  have hLperf' : ⁅autSec L X U, autSec L X U⁆ = autSec L X U := by
    have : Group.IsPerfect ↥L := hLq.1
    have h1 := Group.IsPerfect.range (B5.secHom L hLX hLU)
    rw [B5.range_secHom] at h1
    exact Subgroup.isPerfect_iff.1 h1
  have hirrG : XMod.IsIrrSec ↥(autSec G X U) (⊥ : Subgroup (Sec X U)) ⊤ :=
    B5.isIrrSec_autSec hUX (fun J hJ hUJ hJX => hirr J (B1.le_stabSub_of_invariant hJ) hUJ hJX)
      hGX hGU
  have hautG : autSec G X U = autSec L X U ⊔ autSec H X U := by
    rw [hautL, hautH, ← Subgroup.map_sup, ← Subgroup.subgroupOf_sup le_sup_left le_sup_right,
      Subgroup.subgroupOf_self, autSec_eq_map hGX hGU le_rfl, Subgroup.subgroupOf_self]
  have hirr' : ∀ J ≤ (⊤ : Subgroup (Sec X U)), XMod.IsInv ↥(autSec L X U) J →
      XMod.IsInv ↥(autSec H X U) J → J = ⊥ ∨ J = ⊤ := by
    intro J _ hJL hJH
    have hJG : XMod.IsInv ↥(autSec G X U) J := by
      intro x q hq
      have hx : (x : MulAut (Sec X U)) ∈ autSec L X U ⊔ autSec H X U := hautG ▸ x.2
      exact SmithD391.smul_mem_of_mem_sup (fun a ha s hs => hJL ⟨a, ha⟩ s hs)
        (fun a ha s hs => hJH ⟨a, ha⟩ s hs) hx q hq
    exact hirrG.2 J hJG bot_le le_top
  have hcomm' := commOf_autSec_eq_top hLX hLU hcomm
  have hR : (⊤ : Subgroup (Sec X U)) ≠ ⊥ := hirrG.1.ne'
  set g' := B5.secHom L hLX hLU ⟨g, hgL⟩ with hg'
  have hg'L : g' ∈ autSec L X U := by
    rw [← B5.range_secHom L hLX hLU]
    exact ⟨_, rfl⟩
  have hg'4 : g' ^ 2 ^ 2 = 1 := by
    rw [show 2 ^ 2 = 4 by norm_num, hg', ← map_pow]
    have : (⟨g, hgL⟩ : ↥L) ^ 4 = 1 := Subtype.ext (by simpa using hg4)
    rw [this, map_one]
  have hg'2 : ∃ r ∈ (⊤ : Subgroup (Sec X U)), g' ^ 2 • r ≠ r := by
    by_contra hcon
    push Not at hcon
    have hker : (⟨g, hgL⟩ : ↥L) ^ 2 ∈ (B5.secHom L hLX hLU).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact MulEquiv.ext fun r => hcon r trivial
    rw [B5.mem_ker_secHom] at hker
    have hN : ((centSec X U).subgroupOf L).Normal := by
      refine ⟨fun n hn l => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have hlX := hLX l.2
      have hlU := hLU l.2
      refine ⟨(stabSub X).mul_mem ((stabSub X).mul_mem hlX hn.1) ((stabSub X).inv_mem hlX),
        fun w hw => ?_⟩
      have h1 : (l : MulAut W)⁻¹ w ∈ X := ((stabSub X).inv_mem hlX w).2 hw
      have h2 := hn.2 _ h1
      have h3 : (l : MulAut W) ((n : MulAut W) ((l : MulAut W)⁻¹ w) *
          ((l : MulAut W)⁻¹ w)⁻¹) ∈ U := (hlU _).2 h2
      simpa [MulAut.mul_apply, map_mul, map_inv] using h3
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hN with h | h
    · apply hUX.not_ge
      refine hcomm.trans (sup_le ?_ le_rfl)
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨l, hl, w, hw, rfl⟩
      have : (⟨l, hl⟩ : ↥L) ∈ (centSec X U).subgroupOf L := by rw [h]; trivial
      exact this.2 w hw
    · obtain ⟨y, hyL, hgy⟩ := hg2
      apply hgy
      have h1 := Subgroup.mem_center_iff.1 (h (show (⟨g, hgL⟩ : ↥L) ^ 2 ∈
        (centSec X U).subgroupOf L from hker)) ⟨y, hyL⟩
      exact (congrArg Subtype.val h1).symm
  obtain ⟨Y₁, -, hY₁, -, -, h3, hfix⟩ := SmithD39Two.exists_three_copies hQ hLH' hLperf'
    XMod.isInv_top XMod.isInv_top hirr' hcomm' hR hg'L hg'4 hg'2
  exact ⟨Y₁, hY₁, fun P hP => h3 P hP, fun p hp hpY r => hfix p hp hpY r trivial⟩

theorem conj_mem_centSec' {X U : Subgroup W} {h g : MulAut W} (hhX : h ∈ stabSub X)
    (hhU : h ∈ stabSub U) (hg : g ∈ centSec X U) : h * g * h⁻¹ ∈ centSec X U := by
  refine ⟨(stabSub X).mul_mem ((stabSub X).mul_mem hhX hg.1) ((stabSub X).inv_mem hhX),
    fun w hw => ?_⟩
  have h1 : h⁻¹ w ∈ X := ((stabSub X).inv_mem hhX w).2 hw
  have h2 := hg.2 _ h1
  have h3 : h (g (h⁻¹ w) * (h⁻¹ w)⁻¹) ∈ U := (hhU _).2 h2
  simpa [MulAut.mul_apply, map_mul, map_inv] using h3

theorem le_centralizer_of_centSec {K A : Subgroup (MulAut W)} {X U : Subgroup W}
    (hKq : CFSG.IsQuasisimple ↥K) (hKX : K ≤ stabSub X) (hKU : K ≤ stabSub U)
    (hAK : A ≤ Subgroup.normalizer (K : Set (MulAut W))) (hnt : ¬ K ≤ centSec X U) :
    A ⊓ centSec X U ≤ Subgroup.centralizer (K : Set (MulAut W)) := by
  have hperf : ⁅K, K⁆ = K := by
    have : Group.IsPerfect ↥K := hKq.1
    exact Subgroup.commutator_eq_self
  have hN : ((centSec X U).subgroupOf K).Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_centSec' (hKX k.2) (hKU k.2) hn
  have hNc : (centSec X U).subgroupOf K ≤ Subgroup.center ↥K := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hN with h | h
    · exfalso
      apply hnt
      intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (centSec X U).subgroupOf K := by rw [h]; trivial
      exact this
    · exact h
  have hcentral : ∀ z ∈ K ⊓ centSec X U, ∀ l ∈ K, z * l = l * z := by
    intro z hz l hl
    have hz' : (⟨z, hz.1⟩ : ↥K) ∈ (centSec X U).subgroupOf K := hz.2
    have := Subgroup.mem_center_iff.mp (hNc hz') ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  intro a ha
  have haN : ∀ l ∈ K, a * l * a⁻¹ ∈ K := fun l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hAK ha.1)) l).1 hl
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  refine (B5.commute_of_comm_central hperf haN hcentral (fun l hl => ⟨?_, ?_⟩) l hl).symm
  · rw [commutatorElement_def]
    exact K.mul_mem (haN l hl) (K.inv_mem hl)
  · have h1 : l * a⁻¹ * l⁻¹ ∈ centSec X U :=
      conj_mem_centSec' (hKX hl) (hKU hl) ((centSec X U).inv_mem ha.2)
    have h2 : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact (centSec X U).mul_mem ha.2 h1

theorem fixed_eq_fixV (P : Subgroup (MulAut W)) :
    XMod.fixed ↥P (⊤ : Subgroup W) = fixV P := by
  ext w
  exact ⟨fun h p hp => h.2 ⟨p, hp⟩, fun h => ⟨trivial, fun p => h p p.2⟩⟩

theorem nB_top_eq_rkIdx [Finite W] (P : Subgroup (MulAut W)) :
    Z391.nB P (⊤ : Subgroup W) = rkIdx (fixV P) := by
  unfold Z391.nB
  rw [fixed_eq_fixV, top_inf_eq, rk_top]
  have := rk_add_rkIdx (fixV P)
  omega

end Sections

end Elementary

variable {W : Type} [CommGroup W] [Finite W]

theorem le_centralizer_pCoreOf_three {M T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
    (hAC : A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹) :
    A ≤ Subgroup.centralizer
      (CFSG.Open.pCoreOf 3 (M ⊓ Subgroup.centralizer (L : Set (MulAut W))) :
        Set (MulAut W)) := by
  set C := M ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hCdef
  set P := CFSG.Open.pCoreOf 3 C with hPdef
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAMC : A ≤ C := le_inf hS.A_le hAC
  have hPC : P ≤ C := CFSG.LieType.BorelTits.pCoreOf_le 3 C
  have hP3 : IsPGroup 3 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 3 C
  have hPcyc : IsCyclic ↥P :=
    isCyclic_pCoreOf_three_centralizer hS.qsqtk hS.L_le hu' hs hu'3 hu'1 hs2 hsu
  have hnP : ∀ c ∈ C, ∀ g ∈ P, c * g * c⁻¹ ∈ P := fun c hc g hg =>
    (Subgroup.mem_normalizer_iff.1 (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 3 C hc) g).1 hg
  have hAc : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := hS.isA2.isElemAbelian2.1
  by_contra hcon
  obtain ⟨a, haA, hna⟩ := Set.not_subset.1 hcon
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hna
  push Not at hna
  obtain ⟨g, hgP, hga⟩ := hna
  have ha2 : a ^ 2 = 1 := hS.isA2.isElemAbelian2.2 a haA
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by rw [← pow_two, ha2])
  obtain ⟨y, hyP, hy3, hy1, hay⟩ :=
    exists_inv_of_not_comm hP3 ha2 (hnP a (hAMC haA)) hgP (Ne.symm hga)
  have hyC : y ∈ C := hPC hyP
  have hyM : y ∈ M := hyC.1
  have hyL : ∀ x ∈ L, y * x = x * y := fun x hx =>
    ((Subgroup.mem_centralizer_iff.1 hyC.2) x hx).symm
  set B₁ := A ⊓ Subgroup.centralizer ({y} : Set (MulAut W)) with hB₁def
  have hB₁A : B₁ ≤ A := inf_le_left
  have hmemB₁ : ∀ x, x ∈ B₁ ↔ x ∈ A ∧ x * y = y * x := fun x => by
    rw [hB₁def, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  have hsplit : ∀ x ∈ A, x ∈ B₁ ∨ a⁻¹ * x ∈ B₁ := by
    intro x hx
    rcases conj_eq_or_eq_inv hPcyc hyP hy3 hy1 (hnP x (hAMC hx) y hyP) with h | h
    · left
      refine (hmemB₁ x).2 ⟨hx, ?_⟩
      calc x * y = x * y * x⁻¹ * x := by group
        _ = y * x := by rw [h]
    · right
      refine (hmemB₁ _).2 ⟨A.mul_mem (A.inv_mem haA) hx, ?_⟩
      have h1 : a⁻¹ * y⁻¹ * a = y := by
        calc a⁻¹ * y⁻¹ * a = a * y⁻¹ * a⁻¹ := by rw [hainv]
          _ = (a * y * a⁻¹)⁻¹ := by group
          _ = y := by rw [hay, inv_inv]
      calc a⁻¹ * x * y = a⁻¹ * (x * y * x⁻¹) * x := by group
        _ = a⁻¹ * y⁻¹ * a * (a⁻¹ * x) := by rw [h]; group
        _ = y * (a⁻¹ * x) := by rw [h1]
  have haB₁ : a ∉ B₁ := by
    intro h
    have h1 := ((hmemB₁ a).1 h).2
    have h2 : y = y⁻¹ := by
      rw [← hay]
      calc y = a * y * a⁻¹ * (a * a⁻¹) := by rw [mul_inv_cancel, mul_one, h1]; group
        _ = a * y * a⁻¹ := by group
    exact hy1 (eq_one_of_eq_inv_of_pow_three hy3 h2)
  have hrk := rk_eq_add_one_of_split hB₁A haA haB₁ hsplit
  have hrkA := hS.hrkA
  have hB₁ne : B₁ ≠ ⊥ := by
    intro h
    rw [h, rk_bot] at hrk
    omega
  have hB₁M : B₁ ≤ M := hB₁A.trans hS.A_le
  have hB₁L : ∀ b ∈ B₁, ∀ x ∈ L, b * x = x * b := fun b hb x hx =>
    ((Subgroup.mem_centralizer_iff.1 (hAC (hB₁A hb))) x hx).symm
  have hB₁2 : IsPGroup 2 ↥B₁ := hS.isA2.isElemAbelian2.isPGroup.to_le hB₁A
  have hyB₁ : ∀ e ∈ B₁, y * e = e * y := fun e he => ((hmemB₁ e).1 he).2.symm
  let _i := qAct hS.hD.hyp.Mp_normal
  have hQ := hS.quot_sq
  have hT0 := commOf_eq_of_d3Std hS.hD
  set S := XMod.fixed ↥(B₁.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)))
    with hSdef
  set y' : ↥M := ⟨y, hyM⟩ with hy'
  set a' : ↥M := ⟨a, hS.A_le haA⟩ with ha'
  have hy'3 : y' ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  have ha'2 : a' ^ 2 = 1 := Subtype.ext (by simpa using ha2)
  have ha'y' : a' * y' * a'⁻¹ = y'⁻¹ := Subtype.ext (by simpa using hay)
  have hyS : ∃ q ∈ S, y' • q ≠ q := by
    by_contra hcon'
    push Not at hcon'
    exact hy1 (eq_one_of_fix_fixed hS.hD.hyp.Mp_normal hS.exp hS.commV_eq_top hB₁M hB₁2 hyM
      hyL (k := 3) (by decide) hy3 hyB₁ hcon')
  obtain ⟨q₀, hq₀S, hq₀⟩ := hyS
  have hSinv : ∀ x : ↥M, (∀ e ∈ B₁, (x : MulAut W) * e = e * x) → ∀ q ∈ S, x • q ∈ S := by
    intro x hxe q hq
    refine XMod.mem_fixed.2 ⟨trivial, fun e => ?_⟩
    have hc : (e : ↥M) * x = x * (e : ↥M) :=
      Subtype.ext (hxe _ (Subgroup.mem_subgroupOf.1 e.2)).symm
    show (e : ↥M) • x • q = x • q
    rw [smul_smul, hc, mul_smul]
    exact congrArg _ ((XMod.mem_fixed.1 hq).2 e)
  have hzB₁ : ∀ e ∈ Subgroup.zpowers y', ∀ b ∈ B₁, ((e : ↥M) : MulAut W) * b = b * e := by
    intro e he b hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    have h1 : Commute y b := (hyB₁ b hb)
    simpa using (h1.zpow_left n).eq
  have hy'S : ∀ q ∈ S, y' • q ∈ S := hSinv y' hyB₁
  have ha'S : ∀ q ∈ S, a' • q ∈ S := hSinv a' fun e he => hAc a haA e (hB₁A he)
  set R := XMod.commOf ↥(Subgroup.zpowers y') S with hRdef
  have hRS : R ≤ S :=
    XMod.commOf_le_of_isInv fun e q hq => hSinv (e : ↥M) (hzB₁ _ e.2) q hq
  have hconjy : ∀ x : ↥M, x * y' = y' * x → ∀ e ∈ Subgroup.zpowers y', x * e * x⁻¹ ∈
      Subgroup.zpowers y' := by
    intro x hx e he
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [((Commute.zpow_right hx n)).eq, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers y' n
  have hRy : ∀ q ∈ R, y' • q ∈ R :=
    smul_mem_commOf (hconjy y' rfl) hy'S
  have hRa : ∀ q ∈ R, a' • q ∈ R := by
    refine smul_mem_commOf (fun e he => ?_) ha'S
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    rw [← conj_zpow, ha'y', inv_zpow']
    exact Subgroup.zpow_mem_zpowers y' (-n)
  have hRinv : XMod.IsInv ↥(L.subgroupOf M) R := by
    intro l q hq
    have hlL : ((l : ↥M) : MulAut W) ∈ L := l.2
    have hly : (l : ↥M) * y' = y' * (l : ↥M) := Subtype.ext (hyL _ hlL).symm
    refine smul_mem_commOf (hconjy (l : ↥M) hly) (hSinv (l : ↥M) fun e he =>
      (hB₁L e he _ hlL).symm) q hq
  have hRne : R ≠ ⊥ := by
    intro h
    have hmem : (y' • q₀) * q₀⁻¹ ∈ R :=
      XMod.mem_commOf_of_mem (⟨y', Subgroup.mem_zpowers y'⟩ : ↥(Subgroup.zpowers y')) hq₀S
    rw [h, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hq₀ hmem
  have hrkR : rk ↥(tilde L ⊤ V) ≤ rk ↥R := hS.rk_le_of_isInv hRinv hRne
  have hfix : ∀ q ∈ R, y' • q = q → q = 1 := fun q hq hyq =>
    eq_one_of_mem_commOf_of_fix hQ hy'3 hq hyq
  have hT3 : 2 * nB (Subgroup.zpowers a') R = rk ↥R :=
    two_mul_nB_zpowers_eq hQ ha'2 ha'y' hRy hRa hfix
  have h1 : nB (Subgroup.zpowers a') R ≤ nB (Subgroup.zpowers a') S := nB_mono _ hRS
  have ha'A : a' ∈ A.subgroupOf M := haA
  have h2 : nB (Subgroup.zpowers a') S ≤ nB (A.subgroupOf M) S :=
    nB_le_of_le (Subgroup.zpowers_le.2 ha'A) S
  have hUA : ¬ fixV B₁ ≤ fixV A := by
    intro h
    have hmap := map_fixV_eq_fixed hS.hD.hyp.Mp_normal hB₁M hB₁L hT0
    have hAS : ∀ q ∈ S, a' • q = q := by
      intro q hq
      rw [hSdef, ← hmap] at hq
      obtain ⟨w, hw, rfl⟩ := hq
      show (QuotientGroup.mk (a w) : W ⧸ modFix L (⊤ : Subgroup W)) = QuotientGroup.mk w
      rw [h hw a haA]
    have e1 : a' • q₀ = q₀ := hAS q₀ hq₀S
    have e2 : a' • (y' • q₀) = y' • q₀ := hAS _ (hy'S q₀ hq₀S)
    have hay2 : a' * y' = y'⁻¹ * a' := by
      calc a' * y' = a' * y' * a'⁻¹ * a' := by group
        _ = y'⁻¹ * a' := by rw [ha'y']
    have e3 : y' • q₀ = y'⁻¹ • q₀ := by
      rw [← e2, smul_smul, hay2, mul_smul, e1]
    have e4 : (y' * y') • q₀ = q₀ := by
      rw [mul_smul, e3, smul_inv_smul]
    apply hq₀
    calc y' • q₀ = y' • ((y' * y') • q₀) := by rw [e4]
      _ = (y' ^ 3) • q₀ := by rw [smul_smul, pow_succ, pow_two]; group
      _ = q₀ := by rw [hy'3, one_smul]
  have h3 : nB (A.subgroupOf M) S < 2 * (rk ↥A - rk ↥B₁) :=
    nB_fixed_lt hS.hD.hyp.Mp_normal hS.exp hS.hAQ hB₁A hB₁ne hUA hB₁M hB₁L hT0
  have hv3 := hS.hv3
  omega

theorem caseI_false_of (hA23 : A23SQTKListFact) (hSzF : H13.SimpleThreePrimeSuzukiFact)
    {M T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W} {A : Subgroup (MulAut W)}
    {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
    (hSZ : ∀ K : Subgroup (MulAut W), K ∈ cComp M → CFSG.IsQuasisimple ↥K →
      K ≤ Subgroup.centralizer (L : Set (MulAut W)) →
      (∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥K ⧸ Subgroup.center ↥K) 2 n) →
      A ≤ Subgroup.centralizer (K : Set (MulAut W)))
    (hK3 : ∀ K : Subgroup (MulAut W), K ∈ cComp M → CFSG.IsQuasisimple ↥K →
      K ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) →
      3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) → A ≤ Subgroup.centralizer (K : Set (MulAut W)))
    (hAC : A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹) : False := by
  set C := M ⊓ Subgroup.centralizer (L : Set (MulAut W)) with hCdef
  have hAMC : A ≤ C := le_inf hS.A_le hAC
  have hA2 : IsPGroup 2 ↥A := hS.isA2.isElemAbelian2.isPGroup
  rcases exists_moved_piece hS.pCoreOf_two_cent_eq_bot hAMC hA2 hS.isA2.ne_bot
      hS.M_le_normalizer with ⟨p, hp, hp2, hpA⟩ | ⟨K, hK, hKq, hKC, hKA⟩
  · apply hpA
    rw [← Subgroup.le_centralizer_iff]
    by_cases hp3 : p = 3
    · subst hp3
      exact le_centralizer_pCoreOf_three hS hAC hu' hs hu'3 hu'1 hs2 hsu
    · have hp5 : 5 ≤ p := by
        have h2 := hp.two_le
        rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h | h | h | h
        · exact absurd h hp2
        · exact absurd h hp3
        · exact absurd (h ▸ hp) (by norm_num)
        · exact h
      exact hS.le_centralizer_pCoreOf_cent hp hp5
  · apply hKA
    by_cases h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)
    · exact hK3 K hK hKq hKC h3
    · exact hSZ K hK hKq (hKC.trans inf_le_right)
        (suzukiModel_of_le hA23 hSzF hS.qsqtk (hKC.trans inf_le_left) hKq h3)

theorem eq_of_three_dvd {M T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹) {K K' : Subgroup (MulAut W)}
    (hK : K ∈ cComp M) (hKq : CFSG.IsQuasisimple ↥K)
    (hKC : K ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) (hK' : K' ∈ cComp M)
    (hK'q : CFSG.IsQuasisimple ↥K') (hK'C : K' ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (h3' : 3 ∣ Nat.card (↥K' ⧸ Subgroup.center ↥K')) : K = K' := by
  by_contra hne
  have hMq := hS.qsqtk
  have hLM := hS.L_le
  have hcomm := commute_of_mem_cComp hK hKq hK' hK'q hne
  obtain ⟨y, -, hy3, -, -, -⟩ := exists_two_elt_inverting hKq h3
    (isCyclic_sylow_three_of_le hMq hLM hu' hs hu'3 hu'1 hs2 hsu hKC)
  obtain ⟨y', -, hy'3, hy'Z, -, -⟩ := exists_two_elt_inverting hK'q h3'
    (isCyclic_sylow_three_of_le hMq hLM hu' hs hu'3 hu'1 hs2 hsu hK'C)
  have hpow : ∀ {J : Subgroup (MulAut W)} (z : ↥J), orderOf z = 3 → (z : MulAut W) ^ 3 = 1 ∧
      (z : MulAut W) ≠ 1 := by
    intro J z hz
    refine ⟨?_, fun h => ?_⟩
    · have := pow_orderOf_eq_one z
      rw [hz] at this
      exact congrArg Subtype.val this
    · have : z = 1 := Subtype.ext h
      rw [this, orderOf_one] at hz
      norm_num at hz
  obtain ⟨hy3', hy1⟩ := hpow y hy3
  obtain ⟨hy'3', -⟩ := hpow y' hy'3
  refine no_E9_in_centralizer hMq hLM hu' hs hu'3 hu'1 hs2 hsu (hKC y.2) (hK'C y'.2) hy3' hy'3'
    (hcomm _ y.2 _ y'.2) hy1 fun hmem => hy'Z ?_
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hy'K : (y' : MulAut W) ∈ K := by
    rw [← hn]
    exact K.zpow_mem y.2 n
  refine Subgroup.mem_center_iff.2 fun z => Subtype.ext ?_
  exact (hcomm _ hy'K _ z.2).symm

theorem le_normalizer_of_three_dvd {M T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ} (hS : D310USit M T L V t A r k)
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹) {K : Subgroup (MulAut W)}
    (hK : K ∈ cComp M) (hKq : CFSG.IsQuasisimple ↥K)
    (hKC : K ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (h3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K)) :
    M ≤ Subgroup.normalizer (K : Set (MulAut W)) := by
  intro m hm
  set K' := K.map (MulAut.conj m).toMonoidHom with hK'def
  let e : ↥K ≃* ↥K' := K.equivMapOfInjective _ (MulAut.conj m).injective
  have hK'q : CFSG.IsQuasisimple ↥K' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e hKq
  have hK'C : K' ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hS.le_normalizer_cent hm) x).1 (hKC hx)
  have h3' : 3 ∣ Nat.card (↥K' ⧸ Subgroup.center ↥K') := by
    have e' : ↥K ⧸ Subgroup.center ↥K ≃* ↥K' ⧸ Subgroup.center ↥K' :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    rwa [← Nat.card_congr e'.toEquiv]
  have heq : K' = K := eq_of_three_dvd hS hu' hs hu'3 hu'1 hs2 hsu (map_conj_mem_cComp hK hm)
    hK'q hK'C h3' hK hKq hKC h3
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : m * x * m⁻¹ ∈ K' := ⟨x, hx, by simp [MulAut.conj_apply]⟩
    rwa [heq] at this
  · intro hx
    rw [← heq] at hx
    obtain ⟨z, hz, hzx⟩ := hx
    have : z = x := by
      have h1 : m * z * m⁻¹ = m * x * m⁻¹ := by simpa [MulAut.conj_apply] using hzx
      simpa using h1
    rwa [← this]

section KZero

variable {M T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
  {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ}

theorem smul_isoSum_of_comm (hS : D310USit M T L V t A r k) (c : ↥M)
    (hc : ∀ l ∈ L, (c : MulAut W) * l = l * c) :
    letI := qAct hS.hD.hyp.Mp_normal
    c • isoSum (L.subgroupOf M) (tilde L ⊤ V) = isoSum (L.subgroupOf M) (tilde L ⊤ V) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  refine smul_isoSum_eq hS.Λ_normal (iso_smul_of_comm hS.irr.1 fun l hl => ?_)
  exact Subtype.ext (hc _ hl)

theorem smul_smul_isoSum_of_comm (hS : D310USit M T L V t A r k) (c : ↥M)
    (hc : ∀ l ∈ L, (c : MulAut W) * l = l * c) :
    letI := qAct hS.hD.hyp.Mp_normal
    c • (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) =
      (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  have hc' : ∀ l ∈ L, ((tM⁻¹ * c * tM : ↥M) : MulAut W) * l = l * (tM⁻¹ * c * tM : ↥M) := by
    intro l hl
    have hl' : t * l * t⁻¹ ∈ L :=
      ((Subgroup.mem_normalizer_iff.1 (hS.T_le_normalizer hS.htT)) l).1 hl
    have h1 := hc _ hl'
    show t⁻¹ * (c : MulAut W) * t * l = l * (t⁻¹ * c * t)
    calc t⁻¹ * (c : MulAut W) * t * l = t⁻¹ * ((c : MulAut W) * (t * l * t⁻¹)) * t := by group
      _ = t⁻¹ * ((t * l * t⁻¹) * c) * t := by rw [h1]
      _ = l * (t⁻¹ * c * t) := by group
  have h2 := smul_isoSum_of_comm hS _ hc'
  calc c • tM • isoSum (L.subgroupOf M) (tilde L ⊤ V) =
      tM • (tM⁻¹ * c * tM) • isoSum (L.subgroupOf M) (tilde L ⊤ V) := by
        rw [smul_smul, smul_smul]
        congr 1
        group
    _ = tM • isoSum (L.subgroupOf M) (tilde L ⊤ V) := by rw [h2]

@[expose] noncomputable def fixSub (hS : D310USit M T L V t A r k)
    (R : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) : Subgroup (MulAut W) :=
  letI := qAct hS.hD.hyp.Mp_normal
  (⨅ q ∈ R, MulAction.stabilizer ↥M q).map M.subtype

theorem mem_fixSub (hS : D310USit M T L V t A r k)
    {R : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))} {x : MulAut W} (hxM : x ∈ M) :
    letI := qAct hS.hD.hyp.Mp_normal
    x ∈ fixSub hS R ↔ ∀ q ∈ R, (⟨x, hxM⟩ : ↥M) • q = q := by
  let _i := qAct hS.hD.hyp.Mp_normal
  constructor
  · rintro ⟨y, hy, rfl⟩ q hq
    have := (Subgroup.mem_iInf.1 ((Subgroup.mem_iInf.1 hy) q)) hq
    exact this
  · intro h
    refine ⟨⟨x, hxM⟩, Subgroup.mem_iInf.2 fun q => Subgroup.mem_iInf.2 fun hq => h q hq, rfl⟩

theorem exists_ne_isoSum (hS : D310USit M T L V t A r k) {K : Subgroup (MulAut W)}
    (hKC : K ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (htK : ∀ x ∈ K, t⁻¹ * x * t ∈ K ∧ t * x * t⁻¹ ∈ K) (hK : K ≠ ⊥) :
    letI := qAct hS.hD.hyp.Mp_normal
    (∃ x, ∃ hx : x ∈ K, ∃ q ∈ isoSum (L.subgroupOf M) (tilde L ⊤ V),
        (⟨x, (hKC hx).1⟩ : ↥M) • q ≠ q) ∧
      (∃ x, ∃ hx : x ∈ K, ∃ q ∈ (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V),
        (⟨x, (hKC hx).1⟩ : ↥M) • q ≠ q) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set Q₁ := isoSum (L.subgroupOf M) (tilde L ⊤ V) with hQ₁
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  obtain ⟨y, hyK, hy1⟩ := (Subgroup.bot_or_exists_ne_one K).resolve_left hK
  have hKM : K ≤ M := hKC.trans inf_le_left
  have hfaith : ∀ x (hx : x ∈ K), (∀ q ∈ Q₁, (⟨x, hKM hx⟩ : ↥M) • q = q) →
      (∀ q ∈ tM • Q₁, (⟨x, hKM hx⟩ : ↥M) • q = q) → x = 1 := by
    intro x hx h1 h2
    refine hS.faithful (hKM hx)
      (fun l hl => ((Subgroup.mem_centralizer_iff.1 (hKC hx).2) l hl).symm) fun q => ?_
    have hq : q ∈ Q₁ ⊔ tM • Q₁ := by rw [hS.sup_isoSum]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hq
    rw [smul_mul', h1 a ha, h2 b hb]
  have h12 : ∀ x (hx : x ∈ K), (∀ z (hz : z ∈ K), ∀ q ∈ Q₁, (⟨z, hKM hz⟩ : ↥M) • q = q) →
      ∀ q ∈ tM • Q₁, (⟨x, hKM hx⟩ : ↥M) • q = q := by
    intro x hx hall q hq
    obtain ⟨q', hq', rfl⟩ := hq
    have h1 := hall _ (htK x hx).1 q' hq'
    show (⟨x, hKM hx⟩ : ↥M) • tM • q' = tM • q'
    have e : (⟨x, hKM hx⟩ : ↥M) * tM = tM * ⟨t⁻¹ * x * t, hKM (htK x hx).1⟩ :=
      Subtype.ext (by show x * t = t * (t⁻¹ * x * t); group)
    rw [smul_smul, e, mul_smul, h1]
  have h21 : ∀ x (hx : x ∈ K), (∀ z (hz : z ∈ K), ∀ q ∈ tM • Q₁, (⟨z, hKM hz⟩ : ↥M) • q = q) →
      ∀ q ∈ Q₁, (⟨x, hKM hx⟩ : ↥M) • q = q := by
    intro x hx hall q hq
    have h1 := hall _ (htK x hx).2 (tM • q) (Subgroup.smul_mem_pointwise_smul _ _ _ hq)
    have e : tM * (⟨x, hKM hx⟩ : ↥M) = ⟨t * x * t⁻¹, hKM (htK x hx).2⟩ * tM :=
      Subtype.ext (by show t * x = t * x * t⁻¹ * t; group)
    rw [smul_smul, ← e, mul_smul] at h1
    have h2 := congrArg (fun z => tM⁻¹ • z) h1
    simpa using h2
  constructor
  · by_contra hcon
    push Not at hcon
    exact hy1 (hfaith y hyK (hcon y hyK) (h12 y hyK hcon))
  · by_contra hcon
    push Not at hcon
    exact hy1 (hfaith y hyK (h21 y hyK hcon) (hcon y hyK))

theorem exists_ne_fixed_isoSum (hS : D310USit M T L V t A r k) {K E : Subgroup (MulAut W)}
    (hKC : K ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (htK : ∀ x ∈ K, t⁻¹ * x * t ∈ K ∧ t * x * t⁻¹ ∈ K) (hK : K ≠ ⊥) (hKperf : ⁅K, K⁆ = K)
    (hEC : E ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W))) (hE2 : IsPGroup 2 ↥E)
    (hKE : ∀ x ∈ K, ∀ e ∈ E, x * e = e * x) :
    letI := qAct hS.hD.hyp.Mp_normal
    (∃ x, ∃ hx : x ∈ K, ∃ q ∈ XMod.fixed ↥(E.subgroupOf M) ⊤ ⊓
        isoSum (L.subgroupOf M) (tilde L ⊤ V), (⟨x, (hKC hx).1⟩ : ↥M) • q ≠ q) ∧
      (∃ x, ∃ hx : x ∈ K, ∃ q ∈ XMod.fixed ↥(E.subgroupOf M) ⊤ ⊓
        (⟨t, hS.t_mem⟩ : ↥M) • isoSum (L.subgroupOf M) (tilde L ⊤ V),
        (⟨x, (hKC hx).1⟩ : ↥M) • q ≠ q) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set Q₁ := isoSum (L.subgroupOf M) (tilde L ⊤ V) with hQ₁
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  have hKM : K ≤ M := hKC.trans inf_le_left
  have hEM : E ≤ M := hEC.trans inf_le_left
  have hE' : IsPGroup 2 ↥(E.subgroupOf M) := A4.isPGroup_subgroupOf_of_le hEM hE2
  have hcomm : ∀ c : ↥M, (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) →
      ∀ l ∈ L, (c : MulAut W) * l = l * c := fun c hc l hl =>
    ((Subgroup.mem_centralizer_iff.1 hc.2) l hl).symm
  have key : ∀ R : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)),
      (∀ c : ↥M, (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) → c • R = R) →
      (∀ x (hx : x ∈ K), ∀ q ∈ XMod.fixed ↥(E.subgroupOf M) ⊤ ⊓ R,
        (⟨x, hKM hx⟩ : ↥M) • q = q) →
      ∀ x (hx : x ∈ K), ∀ q ∈ R, (⟨x, hKM hx⟩ : ↥M) • q = q := by
    intro R hR hfix
    have hRmem : ∀ c : ↥M, (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) →
        ∀ q ∈ R, c • q ∈ R := by
      intro c hc q hq
      rw [← hR c hc]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hq
    have hle : K ≤ fixSub hS R := by
      rw [← closure_odd_eq_of_perfect hKperf, Subgroup.closure_le]
      rintro y ⟨hyK, hyodd⟩
      rw [SetLike.mem_coe, mem_fixSub hS (hKM hyK)]
      have hyk : (⟨y, hKM hyK⟩ : ↥M) ^ orderOf y = 1 := Subtype.ext (by simp)
      refine fix_of_fix_fixed hS.quot_sq hE' hyodd hyk (fun e he => Subtype.ext ?_)
        (fun e he q hq => hRmem _ (hEC (Subgroup.mem_subgroupOf.1 he)) q hq)
        (hRmem _ (hKC hyK)) fun q hq hqE => hfix y hyK q ⟨⟨trivial, fun e => hqE e e.2⟩, hq⟩
      exact hKE y hyK _ (Subgroup.mem_subgroupOf.1 he)
    intro x hx q hq
    exact (mem_fixSub hS (hKM hx)).1 (hle hx) q hq
  obtain ⟨h1, h2⟩ := exists_ne_isoSum hS hKC htK hK
  constructor
  · by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, q, hq, hne⟩ := h1
    exact hne (key Q₁ (fun c hc => smul_isoSum_of_comm hS c (hcomm c hc)) hcon x hx q hq)
  · by_contra hcon
    push Not at hcon
    obtain ⟨x, hx, q, hq, hne⟩ := h2
    exact hne (key (tM • Q₁) (fun c hc => smul_smul_isoSum_of_comm hS c (hcomm c hc)) hcon x hx
      q hq)

theorem le_stabSub_fixV (hS : D310USit M T L V t A r k) {G : Subgroup (MulAut W)}
    (hGM : G ≤ M) : G ≤ stabSub (fixV L) := by
  refine B1.le_stabSub_of_invariant fun g hg w hw => mem_fixV.2 fun l hl => ?_
  have hl' : g⁻¹ * l * g ∈ L := by
    have h1 := (Subgroup.mem_normalizer_iff.1 (hS.M_le_normalizer (M.inv_mem (hGM hg))) l).1 hl
    rwa [inv_inv] at h1
  have h1 := (mem_fixV.1 hw) _ hl'
  calc l (g w) = g ((g⁻¹ * l * g) w) := by simp [MulAut.mul_apply]
    _ = g w := by rw [h1]

theorem exists_chief_of_ne (hS : D310USit M T L V t A r k) {G K : Subgroup (MulAut W)}
    (hGM : G ≤ M) (hKG : K ≤ G) (hKperf : ⁅K, K⁆ = K)
    {S' : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))}
    (hGS' : letI := qAct hS.hD.hyp.Mp_normal;
      ∀ g (hg : g ∈ G), ∀ q ∈ S', (⟨g, hGM hg⟩ : ↥M) • q ∈ S')
    (hKS' : letI := qAct hS.hD.hyp.Mp_normal;
      ∃ x, ∃ hx : x ∈ K, ∃ q ∈ S', (⟨x, hGM (hKG hx)⟩ : ↥M) • q ≠ q) :
    ∃ U X : Subgroup W, fixV L ≤ U ∧ U ≤ X ∧
      X ≤ S'.comap (QuotientGroup.mk' (modFix L (⊤ : Subgroup W))) ∧
      G ≤ stabSub U ∧ G ≤ stabSub X ∧ ¬ commSub X K ≤ U ∧
      ∀ J : Subgroup W, G ≤ stabSub J → U ≤ J → J ≤ X → J = U ∨ J = X := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set π := QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) with hπ
  have hker : ∀ w : W, π w = 1 ↔ w ∈ fixV L := by
    intro w
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  have hCD : fixV L ≤ S'.comap π := fun w hw => by
    rw [Subgroup.mem_comap, (hker w).2 hw]
    exact S'.one_mem
  have hGD : G ≤ stabSub (S'.comap π) := by
    refine B1.le_stabSub_of_invariant fun g hg w hw => ?_
    rw [Subgroup.mem_comap] at hw ⊢
    exact hGS' g hg (π w) hw
  have hnt : ¬ commSub (S'.comap π) K ≤ fixV L := by
    intro h
    obtain ⟨x, hx, q, hq, hne⟩ := hKS'
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective (modFix L (⊤ : Subgroup W)) q
    have hw : w ∈ S'.comap π := hq
    have h1 : x w * w⁻¹ ∈ fixV L := h (Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩)
    apply hne
    have h2 : π (x w * w⁻¹) = 1 := (hker _).2 h1
    rw [map_mul, map_inv, mul_inv_eq_one] at h2
    exact h2
  exact exists_chief_section_le hKperf hCD (le_stabSub_fixV hS hGM) hGD hnt

theorem le_commSub_sup (hS : D310USit M T L V t A r k) {X U : Subgroup W}
    (hLX : L ≤ stabSub X) (hker : fixV L ≤ U) : X ≤ commSub X L ⊔ U := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set π := QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) with hπ
  have hkerπ : ∀ w : W, π w = 1 ↔ w ∈ fixV L := by
    intro w
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq]
  have hinv : XMod.IsInv ↥(L.subgroupOf M) (X.map π) := by
    rintro l _ ⟨x, hx, rfl⟩
    exact ⟨((l : ↥M) : MulAut W) x, (hLX l.2 x).2 hx, rfl⟩
  have hT0 := commOf_eq_of_d3Std hS.hD (X.map π) hinv
  have hle : X.map π ≤ (commSub X L).map π := by
    rw [← hT0, XMod.commOf_le_iff]
    rintro l _ ⟨x, hx, rfl⟩
    refine ⟨((l : ↥M) : MulAut W) x * x⁻¹, Subgroup.subset_closure ⟨_, l.2, x, hx, rfl⟩, ?_⟩
    rw [map_mul, map_inv]
    rfl
  intro x hx
  obtain ⟨c, hc, hcx⟩ := hle ⟨x, hx, rfl⟩
  have hu : c⁻¹ * x ∈ U := by
    apply hker
    rw [← hkerπ, map_mul, map_inv, hcx, inv_mul_cancel]
  have : x = c * (c⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup hc hu

theorem nB_fixed_le (hS : D310USit M T L V t A r k) {B₁ : Subgroup (MulAut W)} (hB₁A : B₁ ≤ A)
    (hB₁L : ∀ b ∈ B₁, ∀ x ∈ L, b * x = x * b) :
    letI := qAct hS.hD.hyp.Mp_normal
    nB (A.subgroupOf M) (XMod.fixed ↥(B₁.subgroupOf M)
      (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)))) ≤ 2 * (rk ↥A - rk ↥B₁) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  have hB₁M : B₁ ≤ M := hB₁A.trans hS.A_le
  have hrkB : rk ↥B₁ ≤ rk ↥A := rk_mono hB₁A
  by_cases hB₁ : B₁ = ⊥
  · subst hB₁
    have h1 : XMod.fixed ↥((⊥ : Subgroup (MulAut W)).subgroupOf M)
        (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))) = ⊤ := by
      refine eq_top_iff.2 fun q _ => ⟨trivial, fun b => ?_⟩
      have hb : ((b : ↥M) : MulAut W) = 1 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 b.2)
      have hb' : (b : ↥M) = 1 := Subtype.ext hb
      show (b : ↥M) • q = q
      rw [hb', one_smul]
    rw [h1, rk_bot, Nat.sub_zero]
    exact (hS.nB_le_rkIdx hS.A_le).trans hS.rkIdx_le
  · by_cases hUA : fixV B₁ ≤ fixV A
    · have hmap := map_fixV_eq_fixed hS.hD.hyp.Mp_normal hB₁M hB₁L (commOf_eq_of_d3Std hS.hD)
      rw [← hmap]
      have h0 : nB (A.subgroupOf M) ((fixV B₁).map
          (QuotientGroup.mk' (modFix L (⊤ : Subgroup W)))) = 0 := by
        unfold nB
        rw [inf_eq_left.2]
        · exact Nat.sub_self _
        rintro _ ⟨w, hw, rfl⟩
        refine ⟨trivial, fun a => ?_⟩
        show (QuotientGroup.mk (((a : ↥M) : MulAut W) w) : W ⧸ modFix L (⊤ : Subgroup W)) =
          QuotientGroup.mk w
        rw [hUA hw _ (Subgroup.mem_subgroupOf.1 a.2)]
      rw [h0]
      exact Nat.zero_le _
    · exact (nB_fixed_lt hS.hD.hyp.Mp_normal hS.exp hS.hAQ hB₁A hB₁ hUA hB₁M hB₁L
        (commOf_eq_of_d3Std hS.hD)).le

theorem smul_mem_of_mem_sup' (hS : D310USit M T L V t A r k) {G₁ G₂ : Subgroup (MulAut W)}
    (h₁ : G₁ ≤ M) (h₂ : G₂ ≤ M) {S' : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))}
    (hG₁ : letI := qAct hS.hD.hyp.Mp_normal;
      ∀ g (hg : g ∈ G₁), ∀ q ∈ S', (⟨g, h₁ hg⟩ : ↥M) • q ∈ S')
    (hG₂ : letI := qAct hS.hD.hyp.Mp_normal;
      ∀ g (hg : g ∈ G₂), ∀ q ∈ S', (⟨g, h₂ hg⟩ : ↥M) • q ∈ S') :
    letI := qAct hS.hD.hyp.Mp_normal
    ∀ g (hg : g ∈ G₁ ⊔ G₂), ∀ q ∈ S', (⟨g, (sup_le h₁ h₂) hg⟩ : ↥M) • q ∈ S' := by
  let _i := qAct hS.hD.hyp.Mp_normal
  intro g hg q hq
  have hg' : (⟨g, (sup_le h₁ h₂) hg⟩ : ↥M) ∈ G₁.subgroupOf M ⊔ G₂.subgroupOf M := by
    rw [← Subgroup.subgroupOf_sup h₁ h₂]
    exact hg
  exact SmithD391.smul_mem_of_mem_sup (A := G₁.subgroupOf M) (Λ := G₂.subgroupOf M)
    (fun a ha s hs => hG₁ (a : MulAut W) ha s hs)
    (fun a ha s hs => hG₂ (a : MulAut W) ha s hs) hg' q hq

theorem exists_irr_side (hS : D310USit M T L V t A r k)
    (hAC : A ≤ Subgroup.centralizer (L : Set (MulAut W))) {K₀ : Subgroup (MulAut W)}
    (hKq : CFSG.IsQuasisimple ↥K₀) (hKC : K₀ ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (hKn : M ≤ Subgroup.normalizer (K₀ : Set (MulAut W)))
    {R' : Subgroup (W ⧸ modFix L (⊤ : Subgroup W))}
    (hR' : letI := qAct hS.hD.hyp.Mp_normal; ∀ c : ↥M,
      (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) → c • R' = R')
    (hRL : letI := qAct hS.hD.hyp.Mp_normal; XMod.IsInv ↥(L.subgroupOf M) R')
    (hKR : letI := qAct hS.hD.hyp.Mp_normal;
      ∃ x, ∃ hx : x ∈ K₀, ∃ q ∈ XMod.fixed ↥((A ⊓ Subgroup.centralizer
        (K₀ : Set (MulAut W))).subgroupOf M) ⊤ ⊓ R', (⟨x, (hKC hx).1⟩ : ↥M) • q ≠ q)
    {g : MulAut W} (hgL : g ∈ L) (hg4 : g ^ 4 = 1) (hg2 : ∃ h ∈ L, g ^ 2 * h ≠ h * g ^ 2) :
    letI := qAct hS.hD.hyp.Mp_normal
    ∃ (X U : Subgroup W) (Y₁ : Subgroup (Sec X U)), U < X ∧ fixV L ≤ U ∧
      K₀ ≤ stabSub X ∧ K₀ ≤ stabSub U ∧ A ≤ stabSub X ∧ A ≤ stabSub U ∧
      XMod.IsIrr ↥(autSec (K₀ ⊔ A) X U) Y₁ ∧
      (∀ p ∈ autSec (K₀ ⊔ A) X U, (∀ y ∈ Y₁, p • y = y) → ∀ r : Sec X U, p • r = r) ∧
      ¬ K₀ ≤ centSec X U ∧
      A ⊓ centSec X U = A ⊓ Subgroup.centralizer (K₀ : Set (MulAut W)) ∧
      3 * nB (autSec A X U) Y₁ ≤ nB (A.subgroupOf M) (XMod.fixed ↥((A ⊓ Subgroup.centralizer
        (K₀ : Set (MulAut W))).subgroupOf M) ⊤ ⊓ R') := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set B₁ := A ⊓ Subgroup.centralizer (K₀ : Set (MulAut W)) with hB₁def
  set S := XMod.fixed ↥(B₁.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)))
    with hSdef
  set π := QuotientGroup.mk' (modFix L (⊤ : Subgroup W)) with hπ
  have hKM : K₀ ≤ M := hKC.trans inf_le_left
  have hAM : A ≤ M := hS.A_le
  have hLM : L ≤ M := hS.L_le
  have hAc : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := hS.isA2.isElemAbelian2.1
  have hpres : ∀ c : ↥M, (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) →
      (∀ b ∈ B₁, (c : MulAut W) * b = b * c) → ∀ q ∈ S ⊓ R', c • q ∈ S ⊓ R' := by
    intro c hc hcB q hq
    refine ⟨⟨trivial, fun b => ?_⟩, ?_⟩
    · have hbc : (b : ↥M) * c = c * (b : ↥M) :=
        Subtype.ext (hcB _ (Subgroup.mem_subgroupOf.1 b.2)).symm
      have hbq : (b : ↥M) • q = q := (XMod.mem_fixed.1 hq.1).2 b
      show (b : ↥M) • c • q = c • q
      rw [smul_smul, hbc, mul_smul, hbq]
    · rw [← hR' c hc]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hq.2
  have hLS : ∀ g (hg : g ∈ L), ∀ q ∈ S ⊓ R', (⟨g, hLM hg⟩ : ↥M) • q ∈ S ⊓ R' := by
    intro l hl q hq
    refine ⟨⟨trivial, fun b => ?_⟩, ?_⟩
    · have hbl : (b : ↥M) * ⟨l, hLM hl⟩ = ⟨l, hLM hl⟩ * (b : ↥M) := Subtype.ext
        ((Subgroup.mem_centralizer_iff.1 (hAC (Subgroup.mem_subgroupOf.1 b.2).1)) l hl).symm
      have hbq : (b : ↥M) • q = q := (XMod.mem_fixed.1 hq.1).2 b
      show (b : ↥M) • (⟨l, hLM hl⟩ : ↥M) • q = (⟨l, hLM hl⟩ : ↥M) • q
      rw [smul_smul, hbl, mul_smul, hbq]
    · exact hRL ⟨⟨l, hLM hl⟩, hl⟩ q hq.2
  have hKS : ∀ g (hg : g ∈ K₀), ∀ q ∈ S ⊓ R', (⟨g, hKM hg⟩ : ↥M) • q ∈ S ⊓ R' :=
    fun x hx q hq => hpres ⟨x, hKM hx⟩ (hKC hx)
      (fun b hb => (Subgroup.mem_centralizer_iff.1 hb.2 x hx)) q hq
  have hAS : ∀ g (hg : g ∈ A), ∀ q ∈ S ⊓ R', (⟨g, hAM hg⟩ : ↥M) • q ∈ S ⊓ R' :=
    fun x hx q hq => hpres ⟨x, hAM hx⟩ ⟨hAM hx, hAC hx⟩ (fun b hb => hAc x hx b hb.1) q hq
  set H := K₀ ⊔ A with hHdef
  set G := L ⊔ H with hGdef
  have hHM : H ≤ M := sup_le hKM hAM
  have hGM : G ≤ M := sup_le hLM hHM
  have hHS := smul_mem_of_mem_sup' hS hKM hAM hKS hAS
  have hGS := smul_mem_of_mem_sup' hS hLM hHM hLS hHS
  have hKG : K₀ ≤ G := le_sup_left.trans le_sup_right
  have hAG : A ≤ G := le_sup_right.trans le_sup_right
  have hKperf : ⁅K₀, K₀⁆ = K₀ := by
    have : Group.IsPerfect ↥K₀ := hKq.1
    exact Subgroup.commutator_eq_self
  obtain ⟨U, X, hU, hUX, hXD, hGU, hGX, hKXU, hirr⟩ :=
    exists_chief_of_ne hS hGM hKG hKperf hGS hKR
  have hUX' : U < X := by
    refine lt_of_le_of_ne hUX fun h => hKXU ?_
    rw [h]
    exact commSub_le_of_invariant fun x hx w hw => (hGX (hKG hx) w).2 hw
  have hKcent : ¬ K₀ ≤ centSec X U := by
    intro h
    apply hKXU
    rw [commSub, Subgroup.closure_le]
    rintro _ ⟨x, hx, w, hw, rfl⟩
    exact (h hx).2 w hw
  have hcentA : A ⊓ centSec X U = B₁ := by
    apply le_antisymm
    · intro a ha
      exact ⟨ha.1, le_centralizer_of_centSec hKq (hKG.trans hGX) (hKG.trans hGU)
        (hS.A_le.trans hKn) hKcent ha⟩
    · intro b hb
      refine ⟨hb.1, hGX (hAG hb.1), fun x hx => ?_⟩
      apply hU
      have hxS : π x ∈ S := (hXD hx).1
      have h1 : (⟨b, hAM hb.1⟩ : ↥M) • π x = π x :=
        (XMod.mem_fixed.1 hxS).2 ⟨⟨b, hAM hb.1⟩, hb⟩
      have h2 : π (b x * x⁻¹) = 1 := by
        rw [map_mul, map_inv]
        change (⟨b, hAM hb.1⟩ : ↥M) • π x * (π x)⁻¹ = 1
        rw [h1, mul_inv_cancel]
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, modFix_top_eq] at h2
      exact h2
  have hLH : ∀ l ∈ L, ∀ h ∈ H, l * h = h * l := by
    intro l hl h hh
    have hle : H ≤ Subgroup.centralizer ({l} : Set (MulAut W)) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 (hKC hx).2 l hl).symm
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.1 (hAC hx) l hl).symm
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hh)).symm
  obtain ⟨Y₁, hY₁, h3, hfix⟩ := exists_three_copies_sec hS.exp hUX'
    ((le_sup_left : L ≤ G).trans hGX) ((le_sup_left : L ≤ G).trans hGU)
    ((le_sup_right : H ≤ G).trans hGX) ((le_sup_right : H ≤ G).trans hGU) hLH hS.quasi hirr
    (le_commSub_sup hS ((le_sup_left : L ≤ G).trans hGX) hU) hgL hg4 hg2
  have hAH : autSec A X U ≤ autSec H X U := autSec_mono le_sup_right X U
  have hc1 := h3 _ hAH
  rw [nB_top_eq_rkIdx] at hc1
  have hAmap : (A.subgroupOf M).map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hAM
  have hc2 := rkIdx_fixV_autSec_le_nB (M := M) π (fun g w => rfl) (A.subgroupOf M) hUX
    (by rw [hπ, QuotientGroup.ker_mk', modFix_top_eq]; exact hU)
  rw [hAmap] at hc2
  have hc3 : nB (A.subgroupOf M) (X.map π) ≤ nB (A.subgroupOf M) (S ⊓ R') :=
    nB_mono _ (Subgroup.map_le_iff_le_comap.2 hXD)
  exact ⟨X, U, Y₁, hUX', hU, hKG.trans hGX, hKG.trans hGU, hAG.trans hGX, hAG.trans hGU, hY₁,
    hfix, hKcent, hcentA, hc1.trans (hc2.trans hc3)⟩

theorem exists_small_irr (hS : D310USit M T L V t A r k)
    (hAC : A ≤ Subgroup.centralizer (L : Set (MulAut W))) {K₀ : Subgroup (MulAut W)}
    (hKq : CFSG.IsQuasisimple ↥K₀) (hKC : K₀ ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (hKn : M ≤ Subgroup.normalizer (K₀ : Set (MulAut W)))
    {g : MulAut W} (hgL : g ∈ L) (hg4 : g ^ 4 = 1) (hg2 : ∃ h ∈ L, g ^ 2 * h ≠ h * g ^ 2) :
    ∃ (X U : Subgroup W) (Y₁ : Subgroup (Sec X U)), U < X ∧ fixV L ≤ U ∧
      K₀ ≤ stabSub X ∧ K₀ ≤ stabSub U ∧ A ≤ stabSub X ∧ A ≤ stabSub U ∧
      XMod.IsIrr ↥(autSec (K₀ ⊔ A) X U) Y₁ ∧
      (∀ p ∈ autSec (K₀ ⊔ A) X U, (∀ y ∈ Y₁, p • y = y) → ∀ r : Sec X U, p • r = r) ∧
      ¬ K₀ ≤ centSec X U ∧
      A ⊓ centSec X U = A ⊓ Subgroup.centralizer (K₀ : Set (MulAut W)) ∧
      3 * nB (autSec A X U) Y₁ ≤ rk ↥(autSec A X U) := by
  let _i := qAct hS.hD.hyp.Mp_normal
  set B₁ := A ⊓ Subgroup.centralizer (K₀ : Set (MulAut W)) with hB₁def
  set S := XMod.fixed ↥(B₁.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)))
    with hSdef
  set Q₁ := isoSum (L.subgroupOf M) (tilde L ⊤ V) with hQ₁
  set tM : ↥M := ⟨t, hS.t_mem⟩ with htM
  have hKM : K₀ ≤ M := hKC.trans inf_le_left
  have hAM : A ≤ M := hS.A_le
  have hK : K₀ ≠ ⊥ := by
    have : Nontrivial ↥K₀ := CFSG.LocalCores.isQuasisimple_nontrivial hKq
    exact (Subgroup.nontrivial_iff_ne_bot K₀).1 this
  have hKperf : ⁅K₀, K₀⁆ = K₀ := by
    have : Group.IsPerfect ↥K₀ := hKq.1
    exact Subgroup.commutator_eq_self
  have htK : ∀ x ∈ K₀, t⁻¹ * x * t ∈ K₀ ∧ t * x * t⁻¹ ∈ K₀ := by
    intro x hx
    refine ⟨?_, ((Subgroup.mem_normalizer_iff.1 (hKn hS.t_mem)) x).1 hx⟩
    have h1 := ((Subgroup.mem_normalizer_iff.1 (hKn (M.inv_mem hS.t_mem))) x).1 hx
    rwa [inv_inv] at h1
  have hB₁C : B₁ ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) :=
    fun b hb => ⟨hAM hb.1, hAC hb.1⟩
  have hB₁2 : IsPGroup 2 ↥B₁ := hS.isA2.isElemAbelian2.isPGroup.to_le inf_le_left
  have hKB : ∀ x ∈ K₀, ∀ e ∈ B₁, x * e = e * x := fun x hx e he =>
    (Subgroup.mem_centralizer_iff.1 he.2 x hx)
  obtain ⟨h₁, h₂⟩ := exists_ne_fixed_isoSum hS hKC htK hK hKperf hB₁C hB₁2 hKB
  have hcomm : ∀ c : ↥M, (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) →
      ∀ l ∈ L, (c : MulAut W) * l = l * c := fun c hc l hl =>
    ((Subgroup.mem_centralizer_iff.1 hc.2) l hl).symm
  have hN := normalizes_whole (Q := W ⧸ modFix L (⊤ : Subgroup W)) (L.subgroupOf M)
    hS.Λ_normal
  have hQ₁L : XMod.IsInv ↥(L.subgroupOf M) Q₁ := isInv_isoSum hS.Λ_normal hS.irr.1
  obtain ⟨X₁, U₁, Y₁, hUX₁, hU₁, hKX₁, hKU₁, hAX₁, hAU₁, hY₁, hfix₁, hKc₁, hcent₁, hc₁⟩ :=
    exists_irr_side hS hAC hKq hKC hKn (R' := Q₁)
      (fun c hc => smul_isoSum_of_comm hS c (hcomm c hc)) hQ₁L h₁ hgL hg4 hg2
  obtain ⟨X₂, U₂, Y₂, hUX₂, hU₂, hKX₂, hKU₂, hAX₂, hAU₂, hY₂, hfix₂, hKc₂, hcent₂, hc₂⟩ :=
    exists_irr_side hS hAC hKq hKC hKn (R' := tM • Q₁)
      (fun c hc => smul_smul_isoSum_of_comm hS c (hcomm c hc))
      (XMod.isInv_smul_of_normalizes hN tM hQ₁L) h₂ hgL hg4 hg2
  have hrk : ∀ {X U : Subgroup W}, A ≤ stabSub X → A ≤ stabSub U → A ⊓ centSec X U = B₁ →
      rk ↥(autSec A X U) + rk ↥B₁ = rk ↥A := by
    intro X U hAX hAU hc
    have h := card_autSec_mul hAX hAU
    rw [hc] at h
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h]
  have hrk₁ := hrk hAX₁ hAU₁ hcent₁
  have hrk₂ := hrk hAX₂ hAU₂ hcent₂
  have hAc : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := hS.isA2.isElemAbelian2.1
  have hApres : ∀ R' : Subgroup (W ⧸ modFix L (⊤ : Subgroup W)), (∀ c : ↥M,
      (c : MulAut W) ∈ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) → c • R' = R') →
      ∀ b ∈ A.subgroupOf M, ∀ q ∈ S ⊓ R', b • q ∈ S ⊓ R' := by
    intro R' hR' b hb q hq
    refine ⟨⟨trivial, fun e => ?_⟩, ?_⟩
    · have hbe : (e : ↥M) * b = b * (e : ↥M) :=
        Subtype.ext (hAc _ (Subgroup.mem_subgroupOf.1 e.2).1 _ hb)
      have heq : (e : ↥M) • q = q := (XMod.mem_fixed.1 hq.1).2 e
      show (e : ↥M) • b • q = b • q
      rw [smul_smul, hbe, mul_smul, heq]
    · rw [← hR' b ⟨b.2, hAC hb⟩]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hq.2
  have hd : (S ⊓ Q₁) ⊓ (S ⊓ tM • Q₁) = ⊥ := by
    refine le_bot_iff.1 (le_trans ?_ hS.inf_isoSum.le)
    exact inf_le_inf inf_le_right inf_le_right
  have hsum := SmithD391.nB_sup_of_inf_eq_bot (A.subgroupOf M)
    (hApres Q₁ fun c hc => smul_isoSum_of_comm hS c (hcomm c hc))
    (hApres (tM • Q₁) fun c hc => smul_smul_isoSum_of_comm hS c (hcomm c hc)) hd
  have hmono : nB (A.subgroupOf M) ((S ⊓ Q₁) ⊔ (S ⊓ tM • Q₁)) ≤ nB (A.subgroupOf M) S :=
    nB_mono _ (sup_le inf_le_left inf_le_left)
  have hD7 := nB_fixed_le hS (B₁ := B₁) inf_le_left fun b hb x hx =>
    ((Subgroup.mem_centralizer_iff.1 (hAC hb.1)) x hx).symm
  have hB₁A : rk ↥B₁ ≤ rk ↥A := rk_mono inf_le_left
  have hc₁' : 3 * nB (autSec A X₁ U₁) Y₁ ≤ nB (A.subgroupOf M) (S ⊓ Q₁) := hc₁
  have hc₂' : 3 * nB (autSec A X₂ U₂) Y₂ ≤ nB (A.subgroupOf M) (S ⊓ tM • Q₁) := hc₂
  have hD7' : nB (A.subgroupOf M) S ≤ 2 * (rk ↥A - rk ↥B₁) := hD7
  by_cases h3 : 3 * nB (autSec A X₁ U₁) Y₁ ≤ rk ↥(autSec A X₁ U₁)
  · exact ⟨X₁, U₁, Y₁, hUX₁, hU₁, hKX₁, hKU₁, hAX₁, hAU₁, hY₁, hfix₁, hKc₁, hcent₁, h3⟩
  · refine ⟨X₂, U₂, Y₂, hUX₂, hU₂, hKX₂, hKU₂, hAX₂, hAU₂, hY₂, hfix₂, hKc₂, hcent₂, ?_⟩
    omega

@[expose] def ClifStep : Prop :=
  ∀ {Γ : Type} [Group Γ] [Finite Γ], IsQuotientOfSQTKTC Γ →
    ∀ {Q : Type} [CommGroup Q] [Finite Q] [MulDistribMulAction Γ Q], (∀ q : Q, q ^ 2 = 1) →
    ∀ {K A : Subgroup Γ}, CFSG.IsQuasisimple ↥K → (∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K) →
      (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      ∀ {Y : Subgroup Q}, XMod.IsIrr ↥(K ⊔ A) Y → (∃ k ∈ K, ∃ y ∈ Y, k • y ≠ y) →
        (∃ a ∈ A, ∃ y ∈ Y, a • y ≠ y) →
        3 * nB A Y ≤ rk ↥A - rk ↥(A ⊓ fixingSubgroup Γ (Y : Set Q)) →
        ∃ P : Subgroup Γ, P ≤ K ∧ IsPGroup 3 ↥P ∧ ¬ IsCyclic ↥P

theorem le_centralizer_of_three_dvd_of_clif (hClif : ClifStep) (hS : D310USit M T L V t A r k)
    (hAC : A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹)
    {g : MulAut W} (hgL : g ∈ L) (hg4 : g ^ 4 = 1) (hg2 : ∃ h ∈ L, g ^ 2 * h ≠ h * g ^ 2)
    {K₀ : Subgroup (MulAut W)} (hK : K₀ ∈ cComp M) (hKq : CFSG.IsQuasisimple ↥K₀)
    (hKC : K₀ ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)))
    (h3 : 3 ∣ Nat.card (↥K₀ ⧸ Subgroup.center ↥K₀)) :
    A ≤ Subgroup.centralizer (K₀ : Set (MulAut W)) := by
  by_contra hKA
  have hKn := le_normalizer_of_three_dvd hS hu' hs hu'3 hu'1 hs2 hsu hK hKq hKC h3
  obtain ⟨X, U, Y₁, hUX, -, hKX, hKU, hAX, hAU, hY₁, hfix, hKc, hcent, hcount⟩ :=
    exists_small_irr hS hAC hKq hKC hKn hgL hg4 hg2
  have hKM : K₀ ≤ M := hKC.trans inf_le_left
  have hAM : A ≤ M := hS.A_le
  set H := K₀ ⊔ A with hHdef
  have hHX : H ≤ stabSub X := sup_le hKX hAX
  have hHU : H ≤ stabSub U := sup_le hKU hAU
  set φ := B5.secHom H hHX hHU with hφ
  let _iH : MulDistribMulAction ↥H (Sec X U) := MulDistribMulAction.compHom (Sec X U) φ
  have hact : ∀ (h : ↥H) (q : Sec X U), h • q = φ h q := fun _ _ => rfl
  have hΓ : IsQuotientOfSQTKTC ↥H := isQuotientOfSQTKTC_of_le hS.qsqtk (sup_le hKM hAM)
  have hQ : ∀ q : Sec X U, q ^ 2 = 1 := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow]
      have : x ^ 2 = 1 := Subtype.ext (by simpa using hS.exp (x : W))
      rw [this, QuotientGroup.mk_one]
  set K' := K₀.subgroupOf H with hK'
  set A' := A.subgroupOf H with hA'
  have hφH : ∀ h : ↥H, φ h ∈ autSec H X U := fun h => by
    rw [← B5.range_secHom H hHX hHU]
    exact ⟨h, rfl⟩
  have hK'q : CFSG.IsQuasisimple ↥K' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe (le_sup_left : K₀ ≤ H)).symm hKq
  have hAK' : ∀ a ∈ A', ∀ x ∈ K', a * x * a⁻¹ ∈ K' := by
    intro a ha x hx
    exact ((Subgroup.mem_normalizer_iff.1 (hKn (hAM (Subgroup.mem_subgroupOf.1 ha)))) _).1 hx
  have hAc' : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := fun a ha b hb =>
    Subtype.ext (hS.isA2.isElemAbelian2.1 _ ha _ hb)
  have hA2' : ∀ a ∈ A', a ^ 2 = 1 := fun a ha =>
    Subtype.ext (by simpa using hS.isA2.isElemAbelian2.2 _ ha)
  have htop : K' ⊔ A' = ⊤ := by
    rw [hK', hA', ← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hY' : XMod.IsIrr ↥(K' ⊔ A') Y₁ := by
    refine isIrr_of_surj (Λ' := ↥(K' ⊔ A')) (Λ := ↥(autSec H X U))
      (fun x => ⟨φ (x : ↥H), hφH x⟩) ?_ (fun x q => rfl) hY₁
    rintro ⟨y, hy⟩
    rw [← B5.range_secHom H hHX hHU] at hy
    obtain ⟨h, rfl⟩ := hy
    exact ⟨⟨h, by rw [htop]; trivial⟩, rfl⟩
  have htriv : ∀ h : ↥H, (∀ y ∈ Y₁, h • y = y) → (h : MulAut W) ∈ centSec X U := by
    intro h hhY
    have h1 := hfix (φ h) (hφH h) hhY
    have h2 : h ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact MulEquiv.ext fun r => h1 r
    exact (B5.mem_ker_secHom H hHX hHU h).1 h2
  have hKY' : ∃ x ∈ K', ∃ y ∈ Y₁, x • y ≠ y := by
    by_contra hcon
    push Not at hcon
    exact hKc fun x hx => htriv ⟨x, (le_sup_left : K₀ ≤ H) hx⟩ (hcon _ hx)
  have hAY' : ∃ a ∈ A', ∃ y ∈ Y₁, a • y ≠ y := by
    by_contra hcon
    push Not at hcon
    apply hKA
    intro a ha
    have h1 : a ∈ A ⊓ centSec X U := ⟨ha, htriv ⟨a, (le_sup_right : A ≤ H) ha⟩ (hcon _ ha)⟩
    rw [hcent] at h1
    exact h1.2
  have hfixeq : XMod.fixed ↥A' (⊤ : Subgroup (Sec X U)) =
      XMod.fixed ↥(autSec A X U) (⊤ : Subgroup (Sec X U)) := by
    have hmap := B5.map_secHom_eq_autSec H hHX hHU (le_sup_right : A ≤ H)
    ext q
    constructor
    · intro hq
      refine ⟨trivial, fun p => ?_⟩
      have hp : (p : MulAut (Sec X U)) ∈ (A.subgroupOf H).map φ := by
        rw [hmap]
        exact p.2
      obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.1 hp
      have h1 := hq.2 ⟨a, ha⟩
      show (p : MulAut (Sec X U)) q = q
      rw [← hpa]
      exact h1
    · intro hq
      refine ⟨trivial, fun a => ?_⟩
      have hmem : φ a ∈ autSec A X U := by
        rw [← hmap]
        exact ⟨a, a.2, rfl⟩
      exact hq.2 ⟨φ a, hmem⟩
  have hnB : nB A' Y₁ = nB (autSec A X U) Y₁ := by
    unfold nB
    rw [hfixeq]
  have hrkA' : rk ↥A' = rk ↥A := by
    unfold rk
    rw [hA', Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ H)).toEquiv]
  have hrkfix : rk ↥(A' ⊓ fixingSubgroup ↥H (Y₁ : Set (Sec X U))) ≤
      rk ↥(A ⊓ centSec X U) := by
    have hle : (A' ⊓ fixingSubgroup ↥H (Y₁ : Set (Sec X U))).map H.subtype ≤
        A ⊓ centSec X U := by
      rintro _ ⟨h, ⟨hA, hfx⟩, rfl⟩
      refine ⟨hA, htriv h fun y hy => ?_⟩
      exact (mem_fixingSubgroup_iff ↥H).1 hfx y hy
    have h1 := rk_mono hle
    unfold rk at h1 ⊢
    rwa [Subgroup.card_map_of_injective H.subtype_injective] at h1
  have hrkaut : rk ↥(autSec A X U) + rk ↥(A ⊓ centSec X U) = rk ↥A := by
    have h := card_autSec_mul hAX hAU
    unfold rk
    rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', h]
  have hr' : 3 * nB A' Y₁ ≤ rk ↥A' - rk ↥(A' ⊓ fixingSubgroup ↥H (Y₁ : Set (Sec X U))) := by
    rw [hnB, hrkA']
    omega
  obtain ⟨P, hPK, hP3, hPnc⟩ := hClif hΓ hQ hK'q hAK' hAc' hA2' hY' hKY' hAY' hr'
  apply hPnc
  have hPW : P.map H.subtype ≤ M ⊓ Subgroup.centralizer (L : Set (MulAut W)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hKC (hPK hx)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc := isCyclic_of_isPGroup_three_of_le hS.qsqtk hS.L_le hu' hs hu'3 hu'1 hs2 hsu
    (hP3.map H.subtype) hPW
  exact isCyclic_of_surjective (P.equivMapOfInjective H.subtype H.subtype_injective).symm
    (P.equivMapOfInjective H.subtype H.subtype_injective).symm.surjective

end KZero

theorem caseI_false_of_clif (h38 : D38Top) (hA23 : A23SQTKListFact)
    (hSzF : H13.SimpleThreePrimeSuzukiFact) (hClif : ClifStep) {M T L : Subgroup (MulAut W)}
    {V : Subgroup W} {t : MulAut W} {A : Subgroup (MulAut W)} {r : ℚ} {k : ℕ}
    (hS : D310USit M T L V t A r k) (hAC : A ≤ Subgroup.centralizer (L : Set (MulAut W)))
    {u' s : MulAut W} (hu' : u' ∈ L) (hs : s ∈ L) (hu'3 : u' ^ 3 = 1) (hu'1 : u' ≠ 1)
    (hs2 : s ^ 2 = 1) (hsu : s * u' * s⁻¹ = u'⁻¹)
    {g : MulAut W} (hgL : g ∈ L) (hg4 : g ^ 4 = 1) (hg2 : ∃ h ∈ L, g ^ 2 * h ≠ h * g ^ 2) :
    False :=
  caseI_false_of hA23 hSzF hS (fun _ hK hKq hKL hSz => sz_le_centralizer h38 hS hK hKq hKL hSz)
    (fun _ hK hKq hKC h3 => le_centralizer_of_three_dvd_of_clif hClif hS hAC hu' hs hu'3 hu'1
      hs2 hsu hgL hg4 hg2 hK hKq hKC h3) hAC hu' hs hu'3 hu'1 hs2 hsu

end CFSG.Quasithin.SmithD310U
