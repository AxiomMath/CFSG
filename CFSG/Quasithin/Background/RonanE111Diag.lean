module

public import CFSG.Quasithin.EmptyFaithful.E111RMain

public section

namespace CFSG.Quasithin.RonanE111

open CFSG.Open CFSG.Quasithin.E2.E22N.E111R

@[expose] def actOn {G : Type} [Group G] (S A : Subgroup G) : Subgroup (MulAut ↥S) :=
  (conjAut (inf_le_right : A ⊓ Subgroup.normalizer (S : Set G) ≤
    Subgroup.normalizer (S : Set G))).range

section Semi

variable {Q : Type} [Group Q] [Finite Q]

theorem card_barRad_le' {n : ℕ} {B D₀ : Subgroup Q} (hBN : B ≤ Subgroup.normalizer (D₀ : Set Q))
    (hB : IsElemAbelian 2 B)
    (hBC : B ⊓ Subgroup.centralizer (D₀ : Set Q) ≤ CFSG.solvableRadical Q)
    (hrank : Nat.card ↥(conjAut hBN).range ≤ 2 ^ n) :
    Nat.card ↥(E1.barRad Q B) ≤ 2 ^ n := by
  set φ := conjAut hBN with hφ
  set ψ := (QuotientGroup.mk' (CFSG.solvableRadical Q)).comp B.subtype with hψ
  have hrange : E1.barRad Q B = ψ.range := by
    unfold E1.barRad
    rw [hψ, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker ≤ ψ.ker := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb ⊢
    have hbc : (b : Q) ∈ Subgroup.centralizer (D₀ : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have h1 : (b : Q) * d * (b : Q)⁻¹ = d :=
        congrArg (fun f : MulAut ↥D₀ => ((f ⟨d, hd⟩ : ↥D₀) : Q)) hb
      calc d * b = b * d * (b : Q)⁻¹ * b := by rw [h1]
        _ = b * d := by group
    rw [hψ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hBC ⟨b.2, hbc⟩
  have h1 : Nat.card ψ.range ≤ Nat.card φ.range := by
    rw [← Subgroup.index_ker, ← Subgroup.index_ker]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hker)
  rw [hrange]
  exact h1.trans hrank

end Semi

namespace DiagSetting

variable {G : Type} [Group G] [Finite G] {X T A S C : Subgroup G}
  (h : CFSG.Quasithin.E2.E22N.E111R.DiagSetting X T A S C) [Fintype ↥C]
include h

theorem card_barRad_le_diagK' {n : ℕ} (hA : C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A)
    (hrank : Nat.card ↥(actOn S A) ≤ 2 ^ n) :
    Nat.card ↥(E1.barRad ↥(diagK T A S C h.diagComm)
      (A.subgroupOf (diagK T A S C h.diagComm))) ≤ 2 ^ n := by
  set K := diagK T A S C h.diagComm
  have hdK : diagSub S C h.diagComm ≤ K := h.diag_le_diagE.trans h.diagE_le_diagK
  have hAN := h.le_normalizer_diag hA
  have hBN : A.subgroupOf K ≤ Subgroup.normalizer
      (((diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) := by
    intro a ha
    rw [mem_normalizer_subgroupOf_iff, inf_eq_left.mpr hdK]
    exact hAN (Subgroup.mem_subgroupOf.mp ha)
  have hB : IsElemAbelian 2 (A.subgroupOf K) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
    · exact h.comm (Subgroup.mem_subgroupOf.mp x.2) (Subgroup.mem_subgroupOf.mp y.2)
    · have := h.elem.2 _ (Subgroup.mem_subgroupOf.mp hx)
      simpa using this
  have hBC : A.subgroupOf K ⊓ Subgroup.centralizer
      (((diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) ≤
      CFSG.solvableRadical ↥K := by
    rw [h.solvableRadical_diagK]
    intro x hx
    have hx1 : x ∈ A.subgroupOf K := hx.1
    have hx2 : x ∈ Subgroup.centralizer
        (((diagSub S C h.diagComm).subgroupOf K : Subgroup ↥K) : Set ↥K) := hx.2
    rw [mem_centralizer_subgroupOf_iff hdK] at hx2
    rw [mem_centralizer_subgroupOf_iff h.diagE_le_diagK]
    exact h.inf_centralizer_le ⟨Subgroup.mem_subgroupOf.mp hx1, hx2⟩
  have hδinj := diagHom_injective h.diagComm h.center_trivial
  set ι : ↥S ≃* ↥(diagSub S C h.diagComm) := MonoidHom.ofInjective hδinj with hι
  set e : ↥((diagSub S C h.diagComm).subgroupOf K) ≃* ↥S :=
    (Subgroup.subgroupOfEquivOfLe hdK).trans ι.symm with he
  have hdiagSub : ∀ s : ↥S, diagHom S C h.diagComm s ∈ diagSub S C h.diagComm :=
    fun s => ⟨s, rfl⟩
  have hdiagK : ∀ s : ↥S, diagHom S C h.diagComm s ∈ K := fun s => hdK (hdiagSub s)
  have hdiagMem : ∀ s : ↥S, (⟨diagHom S C h.diagComm s, hdiagK s⟩ : ↥K) ∈
      (diagSub S C h.diagComm).subgroupOf K :=
    fun s => Subgroup.mem_subgroupOf.mpr (hdiagSub s)
  have hes : ∀ s : ↥S, ((e.symm s : ↥((diagSub S C h.diagComm).subgroupOf K)) : G) =
      diagHom S C h.diagComm s := by
    intro s
    have h1 : e ⟨⟨diagHom S C h.diagComm s, hdiagK s⟩, hdiagMem s⟩ = s := by
      rw [he, MulEquiv.trans_apply, MulEquiv.symm_apply_eq]
      apply Subtype.ext
      exact rfl
    have h2 : e.symm s = ⟨⟨diagHom S C h.diagComm s, hdiagK s⟩, hdiagMem s⟩ := by
      rw [MulEquiv.symm_apply_eq]
      exact h1.symm
    exact congrArg (fun z : ↥((diagSub S C h.diagComm).subgroupOf K) => ((z : ↥K) : G)) h2
  have hmap : Subgroup.map (MulAut.congr e).toMonoidHom (conjAut hBN).range ≤ actOn S A := by
    rintro _ ⟨f, ⟨b, rfl⟩, rfl⟩
    have hbA : ((b : ↥K) : G) ∈ C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) := by
      rw [hA]
      exact Subgroup.mem_subgroupOf.mp b.2
    have hUV : A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (C : Set G) :=
      le_normalizer_of_comm fun x hx y hy => h.comm hx.1 (h.CA hy)
    obtain ⟨c, hc, u, hu, hbcu⟩ := exists_mul_of_mem_sup hUV hbA
    have hucomm : ∀ c' ∈ C, u * c' = c' * u := fun c' hc' => h.comm hu.1 (h.CA hc')
    have hus : ∀ s : ↥S, u * (s : G) * u⁻¹ ∈ S := fun s =>
      (Subgroup.mem_normalizer_iff.mp hu.2 (s : G)).mp s.2
    have hfy : ∀ s : ↥S, (((conjAut hBN) b (e.symm s) :
        ↥((diagSub S C h.diagComm).subgroupOf K)) : G) =
        diagHom S C h.diagComm ⟨u * (s : G) * u⁻¹, hus s⟩ := by
      intro s
      calc (((conjAut hBN) b (e.symm s) : ↥((diagSub S C h.diagComm).subgroupOf K)) : G)
          = ((b : ↥K) : G) * (((e.symm s) : ↥((diagSub S C h.diagComm).subgroupOf K)) : G) *
              ((b : ↥K) : G)⁻¹ := rfl
        _ = (c * u) * diagHom S C h.diagComm s * (c * u)⁻¹ := by rw [hbcu, hes s]
        _ = c * (u * diagHom S C h.diagComm s * u⁻¹) * c⁻¹ := by group
        _ = c * diagHom S C h.diagComm ⟨u * (s : G) * u⁻¹, hus s⟩ * c⁻¹ := by
            rw [conj_diagHom_of_comm h.diagComm s hu.2 hucomm]
        _ = diagHom S C h.diagComm ⟨u * (s : G) * u⁻¹, hus s⟩ :=
            conj_diagHom_of_mem h.diagComm _ hc
    have hfin : ∀ s : ↥S, e ((conjAut hBN) b (e.symm s)) = ⟨u * (s : G) * u⁻¹, hus s⟩ := by
      intro s
      have h3 : (conjAut hBN) b (e.symm s) = e.symm ⟨u * (s : G) * u⁻¹, hus s⟩ :=
        Subtype.ext (Subtype.ext ((hfy s).trans (hes ⟨u * (s : G) * u⁻¹, hus s⟩).symm))
      rw [h3, MulEquiv.apply_symm_apply]
    unfold actOn
    refine MonoidHom.mem_range.mpr ⟨⟨u, hu⟩, MulEquiv.ext fun s => Subtype.ext ?_⟩
    exact (congrArg (fun z : ↥S => (z : G)) (hfin s)).symm
  haveI : Finite (MulAut ↥S) := MulEquiv.finite_left
  have hinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hmapcard : Nat.card ↥(Subgroup.map (MulAut.congr e).toMonoidHom (conjAut hBN).range) =
      Nat.card ↥(conjAut hBN).range := Subgroup.card_map_of_injective hinj
  have hle : Nat.card ↥(conjAut hBN).range ≤ Nat.card ↥(actOn S A) :=
    hmapcard.symm.le.trans (Subgroup.card_le_of_le hmap)
  exact card_barRad_le' hBN hB hBC (hle.trans hrank)

theorem isE_diagK' {n : ℕ} (hn : 1 ≤ n)
    (hcase : (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A ∧
        ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) ∧
        Nat.card ↥(actOn S A) ≤ 2 ^ n) ∨
      (A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) ∧
        (C ⊔ (A ⊓ Subgroup.normalizer (S : Set G))).relIndex A = 2)) :
    E1.IsE n ⊤ T A (diagK T A S C h.diagComm) := by
  have hτ : E1.tauOf ⊤ T A ≤ T ⊓ diagK T A S C h.diagComm :=
    (CFSG.Quasithin.E2.E22N.E111R.tauOf_le
      (CFSG.Quasithin.E2.E22N.E111R.pCoreOf_two_eq_bot h.red) T A).trans
      (le_inf inf_le_left h.le_diagK)
  refine ⟨le_top, hτ, h.isSylowIn_diagK, Or.inr ?_⟩
  rcases hcase with ⟨hA, hV, hrank⟩ | ⟨hV, hidx⟩
  · exact ⟨h.eTwo_diagK (Or.inl (h.diag_eq_commutator hA hV)),
      card_barRad_le_diagK' h hA hrank⟩
  · have h2 := h.card_barRad_diagK_eq hV hidx
    refine ⟨h.eTwo_diagK (Or.inr ⟨h.not_le_normalizer_diag hidx, h2⟩), ?_⟩
    rw [h2]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

end DiagSetting

theorem exists_member_comp {G : Type} [Group G] [Finite G] {X T : Subgroup G}
    (hR : CFSG.Quasithin.Vol2.Ch11.SecB.E111Reduced G X T) {n : ℕ} (hn : 1 ≤ n)
    {A : Subgroup G} (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    {S : Subgroup G} (hS : E2.E22N.E111R.IsComp X S)
    (hAS : ¬ A ≤ Subgroup.centralizer (S : Set G))
    (hrank : ¬ A ⊓ Subgroup.normalizer (S : Set G) ≤ Subgroup.centralizer (S : Set G) →
      Nat.card ↥(actOn S A) ≤ 2 ^ n) :
    ∃ K : Subgroup G, E1.IsE n ⊤ T A K ∧
      ∀ x ∈ S, ∃ y ∈ K, x⁻¹ * y ∈ Subgroup.centralizer (S : Set G) := by
  set V := A ⊓ Subgroup.normalizer (S : Set G) with hVdef
  obtain ⟨Z, hZA, hZV, hZVA⟩ := exists_compl hA (inf_le_left : V ≤ A)
  by_cases hV : V ≤ Subgroup.centralizer (S : Set G)
  ·
    have hZ1 : Z ≠ ⊥ := by
      intro hZ
      rw [hZ, bot_sup_eq] at hZVA
      exact hAS (hZVA ▸ hV)
    obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ Z, z ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hZ1 ((Subgroup.eq_bot_iff_forall Z).mpr hc)
    have hZe := isElemAbelian_of_le hA hZA
    obtain ⟨C, hCZ, hCz, hCzZ⟩ := exists_compl hZe (Subgroup.zpowers_le.mpr hzZ)
    have hidx := relIndex_eq_two hA hZA hZV inf_le_left hzZ hz1 hCZ hCz hCzZ hZVA
    have hset : E2.E22N.E111R.DiagSetting X T A S C :=
      ⟨hR, hAT, hA, hS, hCZ.trans hZA, le_bot_iff.mp ((inf_le_inf_right _ hCZ).trans hZV.le)⟩
    let _ : Fintype ↥C := Fintype.ofFinite _
    exact ⟨_, hset.isE_diagK hn (Or.inr ⟨hV, hidx⟩), fun x hx => by
      obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
      exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩⟩
  ·
    have hset : E2.E22N.E111R.DiagSetting X T A S Z := ⟨hR, hAT, hA, hS, hZA, hZV⟩
    let _ : Fintype ↥Z := Fintype.ofFinite _
    exact ⟨_, DiagSetting.isE_diagK' hset hn (Or.inl ⟨hZVA, hV, hrank hV⟩), fun x hx => by
      obtain ⟨y, hy, hc⟩ := hset.exists_diag x hx
      exact ⟨y, hset.diag_le_diagE.trans hset.diagE_le_diagK hy, hc⟩⟩

end CFSG.Quasithin.RonanE111
