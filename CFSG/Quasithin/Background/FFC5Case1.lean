module

public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingSymmetric
public import CFSG.Quasithin.Background.B56Inputs
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.FFC4Res

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open

section Case1

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem centerOf_le_genFitting (G : Subgroup (MulAut V)) : centerOf G ≤ quasithinGenFitting G := by
  unfold quasithinGenFitting
  refine le_sup_of_le_left (le_sSup ⟨inf_le_left, ?_, ?_⟩)
  · refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hz : (g : MulAut V) * (x : MulAut V) * (g : MulAut V)⁻¹ = (x : MulAut V) :=
      mul_inv_eq_iff_eq_mul.2 (Subgroup.mem_centralizer_iff.1 hx.2 (g : MulAut V) g.2)
    simpa [hz] using hx
  · have : IsMulCommutative ↥(centerOf G) := ⟨⟨fun a b => Subtype.ext
      (Subgroup.mem_centralizer_iff.1 b.2.2 _ a.2.1)⟩⟩
    infer_instance

theorem sqtk_of_le (hA21 : AsA21SQTKSection) {G L : Subgroup (MulAut V)}
    (hq : IsQuotientOfSQTKTauCeti ↥G) (hLG : L ≤ G) (hLq : CFSG.IsQuasisimple ↥L) :
    SQTKGroup ↥L := by
  obtain ⟨S, _, _, hst, hkg, φ, hφ⟩ := IsQuotientOfSQTKTauCeti.of_le hLG hq
  have hlayer : CFSG.layer ↥(⊤ : Subgroup ↥L) = ⊤ :=
    B5.layer_eq_top_of_quasisimple
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv (G := ↥L)).symm hLq)
  have h2 : IsPGroup 2 (↥L ⧸ (⊤ : Subgroup ↥L)) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨0, ?_⟩
    rw [pow_zero, pow_one, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_top _
  exact hA21 S ⟨hst, hkg⟩ ⊤ ↥L (φ.comp (⊤ : Subgroup S).subtype)
    (hφ.comp (Subgroup.topEquiv (G := S)).surjective) ⊤ hlayer h2

theorem genFitting_eq_of_quot {G L : Subgroup (MulAut V)} (hLG : L ≤ G)
    (hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L) (hLq : CFSG.IsQuasisimple ↥L)
    (h2 : ∀ y ∈ G, y ^ 2 ∈ L) (hO2 : pCoreOf 2 G = ⊥) : quasithinGenFitting G = L :=
  B1Red.quasithinGenFitting_eq_of_two_quot hLG hn (B1Red.isQuasisimple_to_open hLq) h2 hO2

theorem b56Case1_of_split (hB51 : AsB51) (hA21 : AsA21SQTKSection) {G L : Subgroup (MulAut V)}
    (hc : B56Counterex G) (hLG : L ≤ G) (hn : ∀ y ∈ G, ∀ l ∈ L, y * l * y⁻¹ ∈ L)
    (hLq : CFSG.IsQuasisimple ↥L) (h2 : ∀ y ∈ G, y ^ 2 ∈ L)
    (hlist : B56QuasisimpleList ↥L) : B56Case1 G := by
  have hF : quasithinGenFitting G = L := genFitting_eq_of_quot hLG hn hLq h2 hc.hyp.1
  have hZ : centerOf G ≤ L := hF ▸ centerOf_le_genFitting G
  have hq := isQuotientOfSQTKTauCeti_of_b53 hc.hyp
  have hSQ : SQTKGroup ↥L := sqtk_of_le hA21 hq hLG hLq
  have hyp : B51Hyp G L :=
    ⟨by rw [hF, sup_eq_left.2 hZ], hLq, hSQ, hLG, hc.hyp.1, hc.hyp.2.1⟩
  have hconc := hB51 V hc.hV G L hyp
  rw [← hF] at hLq hconc hlist
  exact ⟨hLq, hconc, hlist⟩

omit [Finite V] in
theorem b56List_sl2 {L : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (h : BinaryNaturalSL L U Z 2 n) : B56QuasisimpleList ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  exact Or.inl ⟨n, K, hK, hf, hc, ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩

omit [Finite V] in
theorem b56List_sl3 {L : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (h : BinaryNaturalSL L U Z 3 n) : B56QuasisimpleList ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  exact Or.inr (Or.inl ⟨n, K, hK, hf, hc, ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩)

omit [Finite V] in
theorem b56List_sl3_sum {L : Subgroup (MulAut V)} {U : Subgroup V} {K : Type} [Field K] [Finite K]
    {m : ℕ} (hc : Nat.card K = 2 ^ m) (h : DirectSumOfCopies L U ⊥ (FFModel.nat (CFSG.Assembly.LowTwoRank.StatedSL 3 K)) 2) :
    B56QuasisimpleList ↥L := by
  obtain ⟨I, π, -, -, -, hreal⟩ := h
  have hπ := hreal 0
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  exact Or.inr (Or.inl ⟨m, K, inferInstance, inferInstance, hc,
    ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩)

omit [Finite V] in
theorem b56List_sl3_two {L : Subgroup (MulAut V)}
    (h : Nonempty (↥L ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 2)))) : B56QuasisimpleList ↥L :=
  Or.inr (Or.inl ⟨1, ZMod 2, inferInstance, inferInstance, by simp, h⟩)

omit [Finite V] in
theorem b56List_s5 {L A : Subgroup (MulAut V)} (hLq : CFSG.IsQuasisimple ↥L)
    (hn : ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ ∈ L) (e : ↥(L ⊔ A) ≃* Equiv.Perm (Fin 5)) :
    B56QuasisimpleList ↥L := by
  have hLn : (L.subgroupOf (L ⊔ A)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2 ?_
    refine sup_le (fun l hl => ?_) (fun a ha => ?_)
    · exact Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl),
        fun hx => by
          have := L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
          simpa [mul_assoc] using this⟩
    · exact Subgroup.mem_normalizer_iff.2 fun x => ⟨fun hx => hn a ha x hx, fun hx => by
        have := hn a⁻¹ (A.inv_mem ha) (a * x * a⁻¹) hx
        simpa [mul_assoc] using this⟩
  set L' := L.subgroupOf (L ⊔ A) with hL'
  have eL : ↥L ≃* ↥L' := (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm
  have hq' : CFSG.IsQuasisimple ↥L' := CFSG.LocalCores.isQuasisimple_of_mulEquiv eL hLq
  let P : Subgroup (Equiv.Perm (Fin 5)) := L'.map e.toMonoidHom
  have hPn : P.Normal := Subgroup.Normal.map hLn e.toMonoidHom e.surjective
  have eP : ↥L' ≃* ↥P := L'.equivMapOfInjective e.toMonoidHom e.injective
  have hqP : CFSG.IsQuasisimple ↥P := CFSG.LocalCores.isQuasisimple_of_mulEquiv eP hq'
  have : Group.IsPerfect ↥P := hqP.1
  have : Nontrivial ↥P := CFSG.ComponentClassification.Quasisimple.nontrivial
    (B1Red.isQuasisimple_to_open hqP)
  obtain ⟨-, hPA⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternating.symmetric_perfect_subnormal P
      hPn.isSubnormal
  obtain ⟨e₀, -⟩ := A5Model.exists_mulEquiv_A5_SL2_four
  exact Or.inl ⟨2, GaloisField 2 2, inferInstance, inferInstance, by simpa using A5Model.card_gf4,
    ⟨eL.trans (eP.trans ((MulEquiv.subgroupCongr hPA).trans (e₀.trans
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)))))⟩⟩

end Case1

end FFC

end CFSG.Quasithin
