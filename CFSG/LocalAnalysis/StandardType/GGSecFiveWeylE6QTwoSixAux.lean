module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

section Preimage

variable {G : Type} [Group G]

noncomputable def ggConjPreimage (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) : Subgroup G :=
  (A.comap Bs.normalizerMonoidHom).map (Subgroup.normalizer (Bs : Set G)).subtype

theorem ggConjPreimage_le_normalizer (Bs : Subgroup G) (A : Subgroup (MulAut ↥Bs)) :
    ggConjPreimage Bs A ≤ Subgroup.normalizer (Bs : Set G) :=
  Subgroup.map_subtype_le _

theorem mem_ggConjPreimage_iff {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)}
    (x : Subgroup.normalizer (Bs : Set G)) :
    (x : G) ∈ ggConjPreimage Bs A ↔ Bs.normalizerMonoidHom x ∈ A := by
  rw [ggConjPreimage, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have h : y = x := Subtype.ext hyx
    subst h
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem normalizerMonoidHom_conj {G : Type} [Group G] {Bs : Subgroup G}
    {g : G} (hg : g ∈ Subgroup.normalizer (Bs : Set G))
    (u : Subgroup.normalizer (Bs : Set G)) :
    Bs.normalizerMonoidHom (⟨g, hg⟩ * u * ⟨g, hg⟩⁻¹) =
      ggConjAut Bs hg * Bs.normalizerMonoidHom u * (ggConjAut Bs hg)⁻¹ := by
  ext b
  simp only [MulAut.mul_apply, ggConjAut_apply,
    Subgroup.normalizerMonoidHom_apply_apply_coe,
    inv_apply_of_forall (ggConjAut_apply Bs hg) b, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_mk]
  group

theorem ggConjPreimage_map_conj {G : Type} [Group G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) :
    (ggConjPreimage Bs A).map (MulAut.conj g).toMonoidHom =
      ggConjPreimage Bs (A.map (MulAut.conj (ggConjAut Bs hg)).toMonoidHom) := by
  let N := Subgroup.normalizer (Bs : Set G)
  let gN : N := ⟨g, hg⟩
  apply le_antisymm
  · rintro x hx
    obtain ⟨u, huA, hux⟩ := Subgroup.mem_map.mp hx
    have huN : u ∈ N := ggConjPreimage_le_normalizer Bs A huA
    have huA' : Bs.normalizerMonoidHom (⟨u, huN⟩ : N) ∈ A := by
      rw [← mem_ggConjPreimage_iff (⟨u, huN⟩ : N)]
      exact huA
    have hxu : (MulAut.conj g) u = (gN * ⟨u, huN⟩ * gN⁻¹ : N) := by
      change g * u * g⁻¹ = ↑(gN * ⟨u, huN⟩ * gN⁻¹)
      simpa [gN]
    rw [← hux]
    change (MulAut.conj g) u ∈
      ggConjPreimage Bs (A.map (MulAut.conj (ggConjAut Bs hg)).toMonoidHom)
    rw [hxu]
    refine (mem_ggConjPreimage_iff (gN * ⟨u, huN⟩ * gN⁻¹)).mpr ?_
    rw [normalizerMonoidHom_conj hg ⟨u, huN⟩]
    exact Subgroup.mem_map_of_mem (MulAut.conj (ggConjAut Bs hg)).toMonoidHom huA'
  · rintro x hx
    have hxN : x ∈ N := ggConjPreimage_le_normalizer Bs _ hx
    rw [mem_ggConjPreimage_iff (⟨x, hxN⟩ : N)] at hx
    obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hx
    let xN : N := ⟨x, hxN⟩
    let u : N := gN⁻¹ * xN * gN
    have hxeq : gN * u * gN⁻¹ = xN := by
      ext
      simp [u]
      group
    have hconj := normalizerMonoidHom_conj hg u
    rw [hxeq] at hconj
    have hxval : Bs.normalizerMonoidHom xN =
        ggConjAut Bs hg * a * (ggConjAut Bs hg)⁻¹ := by
      simpa [MulAut.conj_apply] using haeq.symm
    have h1 : ggConjAut Bs hg * Bs.normalizerMonoidHom u * (ggConjAut Bs hg)⁻¹ =
        ggConjAut Bs hg * a * (ggConjAut Bs hg)⁻¹ := by
      rw [← hconj, hxval]
    have h2 : Bs.normalizerMonoidHom u = a := by
      have := congrArg (fun z => (ggConjAut Bs hg)⁻¹ * z * ggConjAut Bs hg) h1
      simpa [mul_assoc] using this
    have huA : Bs.normalizerMonoidHom u ∈ A := by
      rw [h2]
      exact ha
    have humem : (u : G) ∈ ggConjPreimage Bs A := by
      rw [mem_ggConjPreimage_iff u]
      exact huA
    refine Subgroup.mem_map.mpr ⟨(u : G), humem, ?_⟩
    change g * (u : G) * g⁻¹ = x
    simp [u, gN, xN]
    group
end Preimage

section Linear

variable {p : ℕ} [Fact p.Prime] {E : Type} [Group E] {V : Type} [AddCommGroup V]
  [Module (ZMod p) V]

theorem ggLin_apply_ofMul_sub (ι : Additive E ≃+ V) (ψ : MulAut E) (b : E) :
    ggLin (p := p) ι ψ (ι (Additive.ofMul b)) - ι (Additive.ofMul b) =
      ι (Additive.ofMul (ψ b * b⁻¹)) := by
  rw [ggLin_apply_ofMul, ← map_sub, ofMul_mul, ofMul_inv, sub_eq_add_neg]

theorem ggLin_apply_ofMul_eq_iff (ι : Additive E ≃+ V) (ψ : MulAut E) (b c : E) :
    ggLin (p := p) ι ψ (ι (Additive.ofMul b)) = ι (Additive.ofMul c) ↔ ψ b = c := by
  rw [ggLin_apply_ofMul]
  exact ι.injective.eq_iff.trans Additive.ofMul.injective.eq_iff

theorem exists_smul_ggLin_sub_eq_of_forall_mem_zpowers (ι : Additive E ≃+ V)
    (hcomm : ∀ x y : E, x * y = y * x) {ψ : MulAut E} {a : E}
    (hmod : ∀ b : E, b⁻¹ * ψ b ∈ Subgroup.zpowers a) (u : V) :
    ∃ c : ZMod p, ggLin (p := p) ι ψ u - u = c • ι (Additive.ofMul a) := by
  obtain ⟨b, rfl⟩ : ∃ b : Additive E, ι b = u := ι.surjective u
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hmod (Additive.toMul b))
  refine ⟨(k : ZMod p), ?_⟩
  have hψeq : ψ (Additive.toMul b) * (Additive.toMul b)⁻¹ = a ^ k := by
    have h2 : ψ (Additive.toMul b) = Additive.toMul b * a ^ k := by rw [hk]; group
    rw [h2]
    rw [← (show Commute a (Additive.toMul b) from hcomm a (Additive.toMul b)).zpow_left k]
    group
  rw [show b = Additive.ofMul (Additive.toMul b) from (ofMul_toMul b).symm,
    ggLin_apply_ofMul_sub, hψeq, ofMul_zpow, map_zsmul, Int.cast_smul_eq_zsmul (ZMod p)]

end Linear

section Image

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G} {V : Type} [AddCommGroup V]
  [Module (ZMod p) V]

noncomputable def ggLinImage (ι : Additive ↥Bs ≃+ V) (P : Subgroup G) : Submodule (ZMod p) V :=
  AddSubgroup.toZModSubmodule p ((P.subgroupOf Bs).toAddSubgroup.comap ι.symm.toAddMonoidHom)

theorem mem_ggLinImage (ι : Additive ↥Bs ≃+ V) (P : Subgroup G) (v : V) :
    v ∈ ggLinImage (p := p) ι P ↔ ((Additive.toMul (ι.symm v) : ↥Bs) : G) ∈ P :=
  Iff.rfl

theorem ofMul_mem_ggLinImage (ι : Additive ↥Bs ≃+ V) (P : Subgroup G) (b : ↥Bs) :
    ι (Additive.ofMul b) ∈ ggLinImage (p := p) ι P ↔ (b : G) ∈ P := by
  rw [mem_ggLinImage, AddEquiv.symm_apply_apply, toMul_ofMul]

theorem ggLinImage_mono (ι : Additive ↥Bs ≃+ V) {P Q : Subgroup G} (h : P ≤ Q) :
    ggLinImage (p := p) ι P ≤ ggLinImage ι Q := fun v hv =>
  (mem_ggLinImage ι Q v).mpr (h ((mem_ggLinImage ι P v).mp hv))

theorem card_ggLinImage (ι : Additive ↥Bs ≃+ V) (P : Subgroup G) :
    Nat.card (ggLinImage (p := p) ι P) = Nat.card ↥(Bs ⊓ P) := by
  let e : ↥(ggLinImage (p := p) ι P) ≃ ↥(P.subgroupOf Bs) :=
    { toFun := fun v => ⟨Additive.toMul (ι.symm v), (mem_ggLinImage ι P v).mp v.2⟩
      invFun := fun b => ⟨ι (Additive.ofMul b), (ofMul_mem_ggLinImage ι P b).mpr b.2⟩
      left_inv := fun v => Subtype.ext (by simp)
      right_inv := fun b => Subtype.ext (by simp) }
  rw [Nat.card_congr e, ← Subgroup.inf_subgroupOf_left P Bs]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv

theorem span_singleton_eq_ggLinImage (ι : Additive ↥Bs ≃+ V) {x : G} (hx : x ∈ Bs) :
    (ZMod p) ∙ ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs)) = ggLinImage ι (Subgroup.zpowers x) := by
  apply le_antisymm
  · rw [Submodule.span_singleton_le_iff_mem, ofMul_mem_ggLinImage]
    exact Subgroup.mem_zpowers x
  · intro v hv
    obtain ⟨b, rfl⟩ : ∃ b : ↥Bs, ι (Additive.ofMul b) = v :=
      ⟨Additive.toMul (ι.symm v), by simp⟩
    rw [ofMul_mem_ggLinImage] at hv
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hv
    have hb : b = (⟨x, hx⟩ : ↥Bs) ^ k := Subtype.ext (by simpa using hk.symm)
    rw [hb, ofMul_zpow, map_zsmul]
    exact zsmul_mem (Submodule.mem_span_singleton_self _) k

end Image

theorem exists_mulEquiv_eq_mk_of_center_eq_bot {L P : Type*} [Group L] [Group P]
    (hZ : Subgroup.center L = ⊥) (θ : L ⧸ Subgroup.center L ≃* P) :
    ∃ φ : L ≃* P, ∀ l, φ l = θ (QuotientGroup.mk l) :=
  ⟨((QuotientGroup.quotientBot (G := L)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq (G := L) hZ.symm)).trans θ, fun l => by simp⟩

end CFSG.StandardType

end
