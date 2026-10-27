module

public import CFSG.Walter.W67.Section5.Frame5

public section

namespace CFSG.Walter.W67

open scoped MatrixGroups
open CFSG.GorensteinWalter CFSG.Glauberman.Dickson

namespace Borel5

section PSL2

variable {F : Type} [Field F]

@[expose] noncomputable def weyl (F : Type) [Field F] : PSL(2, F) :=
  psl2QuotientMap F (standardSplitWeylSL F)

theorem weyl_mul_self : weyl F * weyl F = 1 := by
  rw [weyl, ← map_mul]
  exact (QuotientGroup.eq_one_iff _).mpr (standardSplitWeylSL_sq_mem_center F)

theorem weyl_ne_one : weyl F ≠ 1 := by
  intro h
  have hc : standardSplitWeylSL F ∈ Subgroup.center SL(2, F) := (QuotientGroup.eq_one_iff _).mp h
  obtain ⟨r, hr2, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have h00 := congrFun (congrFun hr 0) 0
  have h01 := congrFun (congrFun hr 0) 1
  simp [standardSplitWeylSL_coe, Matrix.scalar_apply] at h00 h01

theorem weyl_conj_torus {d : PSL(2, F)} (hd : d ∈ torus F) :
    weyl F * d * (weyl F)⁻¹ = d⁻¹ := by
  obtain ⟨a, rfl⟩ := hd
  change psl2QuotientMap F (standardSplitWeylSL F) * psl2QuotientMap F (splitTorusSLHom F a) *
    (psl2QuotientMap F (standardSplitWeylSL F))⁻¹ = (psl2QuotientMap F (splitTorusSLHom F a))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul, standardSplitWeylSL_conj, ← map_inv, map_inv]

theorem coprime_card_unip_torus [Finite F] (hF2 : ringChar F ≠ 2) :
    Nat.Coprime (Nat.card (unip F)) (Nat.card (torus F)) := by
  rw [psl2UpperUnipotentSubgroup_card]
  have h2 := card_torus hF2 (F := F)
  have hdvd : Nat.card (torus F) ∣ Nat.card F - 1 := ⟨2, by rw [← h2]; ring⟩
  have hpos : 1 ≤ Nat.card F := Nat.card_pos
  have hcop : Nat.Coprime (Nat.card F) (Nat.card F - 1) :=
    (Nat.coprime_self_sub_right hpos).mpr (Nat.coprime_one_right _)
  exact hcop.coprime_dvd_right hdvd

theorem unip_inf_torus [Finite F] (hF2 : ringChar F ≠ 2) : unip F ⊓ torus F = ⊥ :=
  disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard (coprime_card_unip_torus hF2))

theorem card_borel [Finite F] (hF2 : ringChar F ≠ 2) :
    Nat.card (psl2Borel F) = Nat.card (unip F) * Nat.card (torus F) := by
  set Bo := psl2Borel F
  set U := (unip F).subgroupOf Bo
  set T := (torus F).subgroupOf Bo
  have hUn : U.Normal := by
    have := psl2UpperUnipotent_normal_in_borel (K := F)
    exact this
  have hU : Nat.card U = Nat.card (unip F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl2UpperUnipotent_le_borel).toEquiv
  have hT : Nat.card T = Nat.card (torus F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe torus_le_borel).toEquiv
  let φ : T →* Bo ⧸ U := (QuotientGroup.mk' U).comp T.subtype
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hxU : ((x : Bo)) ∈ U := (QuotientGroup.eq_one_iff _).mp hx
    have : ((x : Bo) : PSL(2, F)) ∈ unip F ⊓ torus F := ⟨hxU, x.2⟩
    rw [unip_inf_torus hF2, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext this)
  have hsurj : Function.Surjective φ := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
    have hb := borel_le_unip_sup_torus b.2
    obtain ⟨u, hu, d, hd, hud⟩ :=
      (mem_sup_iff_of_le_normalizer torus_le_normalizer_unip).mp hb
    refine ⟨⟨⟨d, torus_le_borel hd⟩, hd⟩, ?_⟩
    change ((⟨d, torus_le_borel hd⟩ : Bo) : Bo ⧸ U) = (b : Bo ⧸ U)
    rw [QuotientGroup.eq]
    have : (⟨d, torus_le_borel hd⟩ : Bo)⁻¹ * b = ⟨d⁻¹ * u * d, by
        have := mul_mem (mul_mem (Bo.inv_mem (torus_le_borel hd)) (psl2UpperUnipotent_le_borel hu))
          (torus_le_borel hd)
        exact this⟩ := by
      apply Subtype.ext
      change d⁻¹ * (b : PSL(2, F)) = d⁻¹ * u * d
      rw [← hud]
      group
    rw [this]
    change d⁻¹ * u * d ∈ unip F
    have := (Subgroup.mem_normalizer_iff.mp (torus_le_normalizer_unip (inv_mem hd)) u).mp hu
    simpa using this
  have hbij := Nat.card_eq_of_bijective φ ⟨hinj, hsurj⟩
  have hL := Subgroup.card_eq_card_quotient_mul_card_subgroup U
  rw [← hU, ← hT, hbij, hL, mul_comm]

theorem exists_conj_torus [Finite F] (hF2 : ringChar F ≠ 2) {C : Subgroup PSL(2, F)}
    (hC : C ≤ psl2Borel F) (hcard : Nat.card C = Nat.card (torus F)) :
    ∃ g ∈ psl2Borel F, C = (torus F).map (MulAut.conj g).toMonoidHom := by
  set Bo := psl2Borel F
  set U := (unip F).subgroupOf Bo
  have hUn : U.Normal := psl2UpperUnipotent_normal_in_borel (K := F)
  have hU : Nat.card U = Nat.card (unip F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe psl2UpperUnipotent_le_borel).toEquiv
  have hT : Nat.card ((torus F).subgroupOf Bo) = Nat.card (torus F) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe torus_le_borel).toEquiv
  have hCc : Nat.card (C.subgroupOf Bo) = Nat.card C :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC).toEquiv
  have hcop := coprime_card_unip_torus hF2 (F := F)
  have hBo := card_borel hF2 (F := F)
  have hcompT : U.IsComplement' ((torus F).subgroupOf Bo) := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hU, hT, ← hBo]
    · rw [hU, hT]
      exact hcop
  have hcompC : U.IsComplement' (C.subgroupOf Bo) := by
    apply Subgroup.isComplement'_of_coprime
    · rw [hU, hCc, hcard, ← hBo]
    · rw [hU, hCc, hcard]
      exact hcop
  have hidx : Nat.Coprime (Nat.card U) U.index := by
    rw [hcompT.symm.index_eq_card, hU, hT]
    exact hcop
  obtain ⟨g, hg⟩ := SchurZassenhaus.complements_conjugate_of_coprime U _ _ hUn hcompT hcompC hidx
  refine ⟨g, g.2, ?_⟩
  ext x
  constructor
  · intro hx
    have hx' : (⟨x, hC hx⟩ : Bo) ∈ C.subgroupOf Bo := hx
    rw [hg] at hx'
    obtain ⟨y, hy, hyx⟩ := hx'
    refine ⟨y, hy, ?_⟩
    have := congrArg Subtype.val hyx
    simpa using this
  · rintro ⟨y, hy, rfl⟩
    have hyB : (⟨y, torus_le_borel hy⟩ : Bo) ∈ (torus F).subgroupOf Bo := hy
    have hmem : MulAut.conj g (⟨y, torus_le_borel hy⟩ : Bo) ∈ C.subgroupOf Bo := by
      rw [hg]
      exact ⟨_, hyB, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hmem

end PSL2

end Borel5

variable {G : Type} [Group G] [Finite G]

namespace Frame5

variable {s : Std G} (f5 : Frame5 s)

open Borel5

theorem exists_std : ∃ g : PSL(2, GaloisField s.p s.f),
    f5.P₁ = ((unip _).map (MulAut.conj g).toMonoidHom).map (psl2Emb s.iso) ∧
    f5.B = ((torus _).map (MulAut.conj g).toMonoidHom).map (psl2Emb s.iso) := by
  set F := GaloisField s.p s.f
  set ι := psl2Emb s.iso
  have hι : Function.Injective ι := PSL2Sub.emb_injective s.iso
  have hF2 : ringChar F ≠ 2 := by
    rw [ringChar.eq F s.p]
    exact s.p_ne_two
  have hcardF : Nat.card F = s.q := GaloisField.card s.p s.f s.f_pos.ne'
  set P₁' := f5.P₁.comap ι
  set B' := f5.B.comap ι
  have hP₁' : Nat.card P₁' = s.q := (PSL2Sub.card_comap_emb s.iso f5.P₁_le).trans f5.card_P₁
  obtain ⟨Q, hQ⟩ := psl2UpperUnipotent_isSylow F (p := s.p) (f := s.f)
    (GaloisField.card s.p s.f s.f_pos.ne')
  have hP₁p : IsPGroup s.p P₁' := IsPGroup.of_card (n := s.f) (by rw [hP₁']; rfl)
  obtain ⟨S', hS'⟩ := hP₁p.exists_le_sylow
  have hS'eq : (S' : Subgroup PSL(2, F)) = P₁' := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hS'
    rw [hP₁', ← hcardF, Sylow.card_eq_multiplicity S', ← Sylow.card_eq_multiplicity Q, hQ,
      psl2UpperUnipotentSubgroup_card]
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq PSL(2, F) Q S'
  have hP₁g : P₁' = (unip F).map (MulAut.conj g).toMonoidHom := by
    rw [← hS'eq, ← hg, Sylow.coe_subgroup_smul, hQ]
    rfl
  have hB'N : B' ≤ Subgroup.normalizer (P₁' : Set PSL(2, F)) := by
    intro y hy
    have hN : ι y ∈ ι.range ⊓ Subgroup.normalizer ((P₁'.map ι : Subgroup G) : Set G) := by
      rw [PSL2Sub.map_comap_emb s.iso f5.P₁_le]
      exact ⟨⟨y, rfl⟩, f5.B_le_normalizer (Subgroup.mem_sup_left hy)⟩
    rw [← JT.map_normalizer_of_injective ι hι] at hN
    exact (Subgroup.mem_map_iff_mem hι).mp hN
  set C := B'.map (MulAut.conj g⁻¹).toMonoidHom
  have hconjinv : ∀ H : Subgroup PSL(2, F),
      (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
    intro H
    rw [Subgroup.map_map]
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hx
    · intro hy
      exact ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hCB : C ≤ psl2Borel F := by
    rw [← psl2UpperUnipotent_normalizer_eq_borel]
    have h1 : B' ≤ (Subgroup.normalizer (unip F : Set PSL(2, F))).map
        (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_equiv_normalizer_eq, ← hP₁g]
      exact hB'N
    have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) h1
    rwa [hconjinv] at h2
  have hCcard : Nat.card C = Nat.card (torus F) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective,
      PSL2Sub.card_comap_emb s.iso f5.B_le]
    have h1 := f5.card_B
    have h2 := card_torus hF2 (F := F)
    rw [hcardF] at h2
    omega
  obtain ⟨h, hh, hCh⟩ := exists_conj_torus hF2 hCB hCcard
  refine ⟨g * h, ?_, ?_⟩
  · rw [← PSL2Sub.map_comap_emb s.iso f5.P₁_le]
    congr 1
    change P₁' = _
    rw [hP₁g]
    have hhU : (unip F).map (MulAut.conj h).toMonoidHom = unip F := by
      have hhN : h ∈ Subgroup.normalizer (unip F : Set PSL(2, F)) := by
        rw [psl2UpperUnipotent_normalizer_eq_borel]
        exact hh
      ext u
      constructor
      · rintro ⟨v, hv, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hhN v).mp hv
      · intro hu
        refine ⟨h⁻¹ * u * h, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hhN) u).mp hu
        simpa using this
    rw [map_mul]
    change _ = Subgroup.map ((MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom)
      (unip F)
    rw [← Subgroup.map_map, hhU]
  · rw [← PSL2Sub.map_comap_emb s.iso f5.B_le]
    congr 1
    change B' = _
    have hB'C : B' = C.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_map]
      ext y
      constructor
      · intro hy
        exact ⟨y, hy, by simp [MulAut.conj_apply, mul_assoc]⟩
      · rintro ⟨x, hx, rfl⟩
        simpa [MulAut.conj_apply, mul_assoc] using hx
    rw [hB'C, hCh, Subgroup.map_map, map_mul]
    rfl

theorem exists_inverting_involution : ∃ T₁ ∈ s.K, T₁ * T₁ = 1 ∧ T₁ ≠ 1 ∧
    ∀ b ∈ f5.B, T₁ * b * T₁⁻¹ = b⁻¹ := by
  obtain ⟨g, -, hB⟩ := f5.exists_std
  set ι := psl2Emb s.iso
  have hι : Function.Injective ι := PSL2Sub.emb_injective s.iso
  refine ⟨ι (g * weyl _ * g⁻¹), PSL2Sub.emb_mem s.iso _, ?_, ?_, ?_⟩
  · rw [← map_mul]
    have : g * weyl (GaloisField s.p s.f) * g⁻¹ * (g * weyl _ * g⁻¹) = 1 := by
      rw [show g * weyl (GaloisField s.p s.f) * g⁻¹ * (g * weyl _ * g⁻¹) =
        g * (weyl _ * weyl _) * g⁻¹ by group, weyl_mul_self]
      group
    rw [this, map_one]
  · intro h1
    apply weyl_ne_one (F := GaloisField s.p s.f)
    have := hι (h1.trans (map_one ι).symm)
    have := congrArg (fun z => g⁻¹ * z * g) this
    simpa [mul_assoc] using this
  · intro b hb
    rw [hB] at hb
    obtain ⟨y, ⟨d, hd, rfl⟩, rfl⟩ := hb
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hw := weyl_conj_torus hd
    calc g * weyl (GaloisField s.p s.f) * g⁻¹ * (g * d * g⁻¹) *
          (g * weyl (GaloisField s.p s.f) * g⁻¹)⁻¹ =
        g * (weyl _ * d * (weyl _)⁻¹) * g⁻¹ := by group
      _ = (g * d * g⁻¹)⁻¹ := by rw [hw]; group

end Frame5

end CFSG.Walter.W67
