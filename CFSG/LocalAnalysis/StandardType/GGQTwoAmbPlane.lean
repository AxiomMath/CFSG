module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAmbDual
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module

namespace GGQTwoAmbModel

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs : Subgroup G} {x y : G}
  {L H : Subgroup G}

private lemma lu2b_coroot_ne_zero (hp : p = 3) (M : GGQTwoAmbModel p Bs x y L H)
    (k : M.ι) : M.coroot k ≠ 0 := by
  intro h
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have : CharP (ZMod p) 3 := by rw [← hp]; infer_instance
    exact QTwoLin.two_ne_zero_of_charP_three
  apply h2ne
  have h2 := M.toLin.root_coroot_self k
  change M.root k (M.coroot k) = 2 at h2
  rw [← h2, h, map_zero]

private lemma lu2b_root_xV_eq_zero (hp : p = 3) (M : GGQTwoAmbModel p Bs x y L H)
    {k : M.ι} (hk : k ≠ M.a) : M.root k M.xV = 0 := by
  have hfix : M.toLin.simpleRefl k M.xV = M.xV :=
    (M.fixed_lin M.xV).mpr (Submodule.mem_span_singleton_self M.xV) _
      (Subgroup.subset_closure ⟨k, hk, rfl⟩)
  have hfix' : ggLin (p := p) M.model (M.simple k) M.xV = M.xV := by
    rw [M.ggLin_simple k]; exact hfix
  have hz : M.xV - M.root k M.xV • M.coroot k = M.xV := by
    rw [← M.simple_apply k M.xV]; exact hfix'
  have hsmul : M.root k M.xV • M.coroot k = 0 := by
    rwa [sub_eq_self] at hz
  exact (smul_eq_zero.mp hsmul).resolve_right (lu2b_coroot_ne_zero hp M k)

private lemma lu2b_root_y'_eq_zero (hp : p = 3) (M : GGQTwoAmbModel p Bs x y L H)
    {y' : M.V}
    (hy' : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {y'})
    {k : M.ι} (hk : k ≠ M.b) : M.root k y' = 0 := by
  have hfix : M.toLin.simpleRefl k y' = y' :=
    (hy' y').mpr (Submodule.mem_span_singleton_self y') _
      (Subgroup.subset_closure ⟨k, hk, rfl⟩)
  have hfix' : ggLin (p := p) M.model (M.simple k) y' = y' := by
    rw [M.ggLin_simple k]; exact hfix
  have hz : y' - M.root k y' • M.coroot k = y' := by
    rw [← M.simple_apply k y']; exact hfix'
  have hsmul : M.root k y' • M.coroot k = 0 := by
    rwa [sub_eq_self] at hz
  exact (smul_eq_zero.mp hsmul).resolve_right (lu2b_coroot_ne_zero hp M k)

private lemma lu2b_range_pair (M : GGQTwoAmbModel p Bs x y L H) :
    Set.range ![M.xV, M.yV] = ({M.xV, M.yV} : Set M.V) := by
  ext v
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem linearIndependent_xV_yV [Finite G] {B D J K : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hnb : GGNbr p B x D J y K)
    (M : GGQTwoAmbModel p Bs x y L H) : LinearIndependent (ZMod p) ![M.xV, M.yV] := by
  classical
  have hDc : D = Subgroup.closure ({x, y} : Set G) := hnb.2.1
  have hBstar : GGBstar p B Bs := hS.1.1.2.1
  have hBle : B ≤ Bs := hBstar.1
  have hstdPre : LargeEvenStdSubPre p B x L D J := hS.1.1.2.2.1
  have hDle : D ≤ Bs := hstdPre.1.trans hBle
  have hcardD : Nat.card D = p ^ 2 := hstdPre.2.2.1
  have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  set W : Submodule (ZMod p) M.V := Submodule.span (ZMod p) ({M.xV, M.yV} : Set M.V) with hW
  let F : ↥Bs ≃ M.V := Additive.ofMul.trans M.model.toEquiv
  have hF : ∀ d : ↥Bs, F d = M.model (Additive.ofMul d) := fun d => rfl
  have hmem : ∀ d : ↥Bs, F d ∈ W ↔ d ∈ D.subgroupOf Bs := by
    intro d
    rw [hF, hW, hDc, Subgroup.mem_subgroupOf]
    exact (mem_closure_iff M d).symm
  have hcardW : Nat.card W = p ^ 2 := by
    have e : (D.subgroupOf Bs) ≃ W :=
      Equiv.ofBijective
        (fun d : D.subgroupOf Bs => (⟨F d.1, (hmem d.1).mpr d.2⟩ : W))
        ⟨fun a b hab => Subtype.ext (F.injective (Subtype.ext_iff.mp hab)), fun w => by
          obtain ⟨d, hd⟩ := F.surjective w.1
          exact ⟨⟨d, (hmem d).mp (hd.symm ▸ w.2)⟩, Subtype.ext hd⟩⟩
    calc Nat.card W = Nat.card (D.subgroupOf Bs) := (Nat.card_congr e).symm
      _ = Nat.card D := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDle).toEquiv
      _ = p ^ 2 := hcardD
  have hfinW : finrank (ZMod p) W = 2 := by
    have h1 : Nat.card W = Nat.card (ZMod p) ^ finrank (ZMod p) W := natCard_eq_pow_finrank
    rw [Nat.card_zmod] at h1
    have h2 : p ^ finrank (ZMod p) W = p ^ 2 := by rw [← h1, hcardW]
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h2
  rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin, lu2b_range_pair M]
  have hfr : Set.finrank (ZMod p) ({M.xV, M.yV} : Set M.V) = finrank (ZMod p) W := by
    rw [hW]; rfl
  rw [hfr]
  exact hfinW.symm

theorem span_xV_fixedLine_eq (hp : p = 3) (M : GGQTwoAmbModel p Bs x y L H)
    (hbas : GGQTwoAmbBasis M) (hnd : ((M.cartan.det : ℤ) : ZMod p) ≠ 0)
    (hxy : LinearIndependent (ZMod p) ![M.xV, M.yV]) {y' : M.V} (hy'0 : y' ≠ 0)
    (hy' : ∀ v, (∀ g ∈ M.toLin.parab {k | k ≠ M.b}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {y'}) :
    Submodule.span (ZMod p) {M.xV, y'} = Submodule.span (ZMod p) {M.xV, M.yV} := by
  classical
  set W : Submodule (ZMod p) M.V := Submodule.span (ZMod p) ({M.xV, M.yV} : Set M.V) with hW
  set W' : Submodule (ZMod p) M.V := Submodule.span (ZMod p) ({M.xV, y'} : Set M.V) with hW'
  have : FiniteDimensional (ZMod p) ↥W' := by
    rw [hW']
    exact FiniteDimensional.span_of_finite (ZMod p) ((Set.finite_singleton y').insert M.xV)
  have hxV0 : M.xV ≠ 0 := by simpa using hxy.ne_zero 0
  have hax : M.root M.a M.xV ≠ 0 := by
    intro h0
    refine hxV0 (eq_zero_of_root_eq_zero M hbas hnd (fun k => ?_))
    by_cases hk : k = M.a
    · subst hk; exact h0
    · exact lu2b_root_xV_eq_zero hp M hk
  have hby : M.root M.b y' ≠ 0 := by
    intro h0
    refine hy'0 (eq_zero_of_root_eq_zero M hbas hnd (fun k => ?_))
    by_cases hk : k = M.b
    · subst hk; exact h0
    · exact lu2b_root_y'_eq_zero hp M hy' hk
  set u : M.V := (M.root M.a M.xV * M.root M.b y') • M.yV
      - (M.root M.a M.yV * M.root M.b y') • M.xV
      - (M.root M.b M.yV * M.root M.a M.xV) • y' with hu
  have hu0 : u = 0 := by
    apply eq_zero_of_root_eq_zero M hbas hnd
    intro k
    by_cases hka : k = M.a
    · subst hka
      have hy'a : M.root M.a y' = 0 := lu2b_root_y'_eq_zero hp M hy' M.a_ne_b
      conv_lhs =>
        rw [hu, map_sub, map_sub, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
          smul_eq_mul, hy'a]
      simp only [mul_comm, mul_left_comm, zero_mul]
      abel
    · by_cases hkb : k = M.b
      · subst hkb
        have hxb : M.root M.b M.xV = 0 := lu2b_root_xV_eq_zero hp M M.a_ne_b.symm
        conv_lhs =>
          rw [hu, map_sub, map_sub, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, hxb]
        simp only [mul_comm, mul_left_comm, zero_mul]
        abel
      · have hxa : M.root k M.xV = 0 := lu2b_root_xV_eq_zero hp M hka
        have hya : M.root k M.yV = 0 := M.root_yV hp k hka hkb
        have hy'a : M.root k y' = 0 := lu2b_root_y'_eq_zero hp M hy' hkb
        conv_lhs =>
          rw [hu, map_sub, map_sub, map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul,
            smul_eq_mul, hxa, hya, hy'a]
        simp only [mul_comm, zero_mul]
        abel
  have h_eq : (M.root M.a M.xV * M.root M.b y') • M.yV =
      (M.root M.b M.yV * M.root M.a M.xV) • y'
        + (M.root M.a M.yV * M.root M.b y') • M.xV := by
    have h := hu0
    rw [hu] at h
    exact sub_eq_iff_eq_add.mp (sub_eq_zero.mp h)
  have hmem : (M.root M.a M.xV * M.root M.b y') • M.yV ∈ W' := by
    rw [hW', h_eq]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_span_of_mem (by simp)))
      (Submodule.smul_mem _ _ (Submodule.mem_span_of_mem (by simp)))
  have hyV_mem : M.yV ∈ W' := by
    have hs : M.root M.a M.xV * M.root M.b y' ≠ 0 := mul_ne_zero hax hby
    have h1 : M.yV = (M.root M.a M.xV * M.root M.b y')⁻¹ •
        ((M.root M.a M.xV * M.root M.b y') • M.yV) := by
      rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
    rw [h1]
    exact Submodule.smul_mem _ _ hmem
  have hle : W ≤ W' := by
    rw [hW, Submodule.span_le]
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl
    · exact Submodule.mem_span_of_mem (by simp)
    · exact hyV_mem
  have hfinW : finrank (ZMod p) W = 2 := by
    have h := linearIndependent_iff_card_eq_finrank_span.mp hxy
    rw [Fintype.card_fin, lu2b_range_pair M] at h
    have hfr : Set.finrank (ZMod p) ({M.xV, M.yV} : Set M.V) = finrank (ZMod p) W := by
      rw [hW]; rfl
    rw [hfr] at h
    exact h.symm
  have hfinW' : finrank (ZMod p) W' ≤ 2 := by
    have h := finrank_span_le_card (R := ZMod p) ({M.xV, y'} : Set M.V)
    have hcard : ({M.xV, y'} : Set M.V).toFinset.card ≤ 2 := by
      rw [Set.toFinset_insert]
      exact le_trans (Finset.card_insert_le M.xV ({y'} : Set M.V).toFinset) (by simp)
    exact le_trans (by rw [hW']; exact h) hcard
  have hfin' : finrank (ZMod p) W' = 2 :=
    le_antisymm hfinW' (by rw [← hfinW]; exact Submodule.finrank_mono hle)
  exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hfinW, hfin'])).symm

end GGQTwoAmbModel

end CFSG.StandardType

end
