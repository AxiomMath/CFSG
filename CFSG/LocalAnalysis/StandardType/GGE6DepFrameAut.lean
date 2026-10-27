module

public import CFSG.LocalAnalysis.StandardType.GGE6DepFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelActs
public import CFSG.LocalAnalysis.StandardType.GGE6DepNormalizerOfConj
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem closureL_fix_x {g : Mat6} (hg : g ∈ closureL) :
    g.mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    revert i
    decide +kernel
  | one => rw [Matrix.one_mulVec]
  | mul g h _ _ ihg ihh => rw [← Matrix.mulVec_mulVec, ihh, ihg]

private theorem transfer {Bs L : Subgroup G} {x : G}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hxBs : x ∈ Bs)
    (ι : Additive ↥Bs ≃+ Vec6) (hι5 : ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1)
    (hιL : ∀ b : ↥Bs, (b : G) ∈ L ↔ ι (Additive.ofMul b) 5 = 0)
    (Φ : ↥(ggGamma L hBsN).range →* Multiplicative Vec6)
    (hιΦ : ∀ b : ↥Bs, ι (Additive.ofMul b) 5 = 0 →
      coordE.mulVec (ι (Additive.ofMul b)) =
        Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b)))
    {n : G} (hnL : n ∈ L) (hnN : n ∈ Subgroup.normalizer (Bs : Set G)) {g : Mat6}
    (hg5 : ∀ v : Vec6, (g.mulVec v) 5 = v 5)
    (hgx : g.mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3))
    (hgΦ : ∀ h : ↥Bs, (h : G) ∈ L →
      coordE.mulVec (g.mulVec (ι (Additive.ofMul h))) =
        Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnN h)))) :
    ActsAs ι (ggConjAut Bs hnN) g := by
  intro b
  obtain ⟨l, hlL, k, hb⟩ := hBsL (b : G) b.2
  have hlBs : l ∈ Bs := by
    have h1 : l = (b : G) * (x ^ k)⁻¹ := by rw [hb]; group
    rw [h1]
    exact Bs.mul_mem b.2 (Bs.inv_mem (Bs.pow_mem hxBs k))
  have hb' : b = (⟨l, hlBs⟩ : ↥Bs) * (⟨x, hxBs⟩ : ↥Bs) ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_pow]
    exact hb
  have hφxs : (ggConjAut Bs hnN) (⟨x, hxBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs) := by
    apply Subtype.ext
    rw [ggConjAut_apply]
    show n * x * n⁻¹ = x
    have hc : x * n = n * x :=
      Subgroup.mem_centralizer_iff.mp (hLx hnL) x (Set.mem_singleton x)
    rw [← hc]
    group
  have hval : (ggConjAut Bs hnN) b =
      (ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs) * (⟨x, hxBs⟩ : ↥Bs) ^ k := by
    rw [hb', map_mul, map_pow, hφxs]
  have hbvec : ι (Additive.ofMul b) =
      ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs)) + k • Pi.single 5 (1 : ZMod 3) := by
    calc ι (Additive.ofMul b) =
          ι (Additive.ofMul ((⟨l, hlBs⟩ : ↥Bs) * (⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [hb']
      _ = ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs) +
            Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [ofMul_mul]
      _ = ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs)) +
            ι (Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [map_add]
      _ = ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs)) +
            k • ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by rw [ofMul_pow, map_nsmul]
      _ = ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs)) + k • Pi.single 5 (1 : ZMod 3) := by rw [hι5]
  have hφhL : (((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs) : ↥Bs) : G) ∈ L := by
    rw [ggConjAut_apply]
    exact L.mul_mem (L.mul_mem hnL hlL) (L.inv_mem hnL)
  have hLHS5 : (ι (Additive.ofMul ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs)))) 5 = 0 :=
    (hιL ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs))).mp hφhL
  have hRHS5 : (g.mulVec (ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs)))) 5 = 0 := by
    rw [hg5, (hιL (⟨l, hlBs⟩ : ↥Bs)).mp hlL]
  have hih : ι (Additive.ofMul ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs))) =
      g.mulVec (ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs))) := by
    apply coordE_injOn _ _ hLHS5 hRHS5
    rw [hιΦ ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs)) hLHS5,
      hgΦ (⟨l, hlBs⟩ : ↥Bs) hlL]
  calc ι (Additive.ofMul ((ggConjAut Bs hnN) b))
      = ι (Additive.ofMul ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs) *
          (⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [hval]
    _ = ι (Additive.ofMul ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs)) +
          Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [ofMul_mul]
    _ = ι (Additive.ofMul ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs))) +
          ι (Additive.ofMul ((⟨x, hxBs⟩ : ↥Bs) ^ k)) := by rw [map_add]
    _ = ι (Additive.ofMul ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs))) +
          k • ι (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by rw [ofMul_pow, map_nsmul]
    _ = ι (Additive.ofMul ((ggConjAut Bs hnN) (⟨l, hlBs⟩ : ↥Bs))) +
          k • Pi.single 5 (1 : ZMod 3) := by rw [hι5]
    _ = g.mulVec (ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs))) +
          k • Pi.single 5 (1 : ZMod 3) := by rw [hih]
    _ = g.mulVec (ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs))) +
          k • g.mulVec (Pi.single 5 (1 : ZMod 3)) := by rw [hgx]
    _ = g.mulVec (ι (Additive.ofMul (⟨l, hlBs⟩ : ↥Bs)) +
          k • Pi.single 5 (1 : ZMod 3)) := by rw [Matrix.mulVec_add, Matrix.mulVec_smul]
    _ = g.mulVec (ι (Additive.ofMul b)) := by rw [hbvec]

theorem ggE6Dep_automizer_closureL {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hxBs : x ∈ Bs) (hZ : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    (hcard : Nat.card (ggGamma L hBsN).range = 3 ^ 5) {Z : Subgroup ↥L}
    {Φ : ↥(ggGamma L hBsN).range →* Multiplicative (Fin 6 → ZMod 3)} {T : Subgroup ↥L}
    {w : Fin 6 → ↥L} (hmodel : GGE6ThreeWeylModelWith Z (ggGamma L hBsN).range Φ T w)
    (ι : Additive ↥Bs ≃+ Vec6) (hι5 : ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1)
    (hιL : ∀ b : ↥Bs, (b : G) ∈ L ↔ ι (Additive.ofMul b) 5 = 0)
    (hιΦ : ∀ b : ↥Bs, ι (Additive.ofMul b) 5 = 0 →
      coordE.mulVec (ι (Additive.ofMul b)) =
        Multiplicative.toAdd (Φ ((ggGamma L hBsN).rangeRestrict b))) :
    (∀ φ ∈ ggAutomizer L Bs, ∃ g ∈ closureL, ActsAs ι φ g) ∧
      (∀ g ∈ closureL, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ g) := by
  classical
  obtain ⟨hp, hBs, hxBs', hLx, -⟩ := hcfg.tableB_facts
  refine ⟨?_, ?_⟩
  · intro φ hφaut
    obtain ⟨n, hnL, hnN, hφb⟩ := mem_ggAutomizer_iff.mp hφaut
    obtain ⟨-, -, -, -, -, -, -, -, -, hcl10, -, -⟩ := hmodel
    have hφeq : φ = ggConjAut Bs hnN := by
      ext b
      rw [ggConjAut_apply]
      exact hφb b
    have hnN' : MulAut.conj (⟨n, hnL⟩ : ↥L) ∈
        Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) :=
      conj_mem_normalizer_range_ggGamma (X := L) hBsN hnL hnN
    obtain ⟨u, hu⟩ := hcl10 ⟨n, hnL⟩ hnN'
    obtain ⟨g, hg, hgv⟩ := exists_closureL_of_weyl u
    refine ⟨g, hg, ?_⟩
    rw [hφeq]
    refine transfer hBsN hBsL hLx hxBs ι hι5 hιL Φ hιΦ hnL hnN
      (closureL_apply_five hg) (closureL_fix_x hg) ?_
    intro h hhL
    have hv : (ι (Additive.ofMul h)) 5 = 0 := (hιL h).mp hhL
    have hrel : (↑((ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnN h)) : MulAut ↥L) =
        MulAut.conj (⟨n, hnL⟩ : ↥L) * (↑((ggGamma L hBsN).rangeRestrict h) : MulAut ↥L) *
          (MulAut.conj (⟨n, hnL⟩ : ↥L))⁻¹ := by
      have h1 : ggConjAut Bs hnN h =
          (⟨n * (h : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnN h).mp h.2⟩ : ↥Bs) :=
        Subtype.ext (ggConjAut_apply Bs hnN h)
      rw [h1]
      simp only [MonoidHom.coe_rangeRestrict]
      exact ggGamma_conj L hBsN ⟨n, hnL⟩ h _
    exact (hgv (ι (Additive.ofMul h)) hv).trans
      ((congrArg (TableBExc.E6Three.adAct .E6 3 u) (hιΦ h hv)).trans
        (hu ((ggGamma L hBsN).rangeRestrict h)
          ((ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnN h)) hrel).symm)
  · intro g hg
    induction hg using Submonoid.closure_induction with
    | mem g hg =>
      obtain ⟨j, rfl⟩ := hg
      obtain ⟨-, -, -, -, -, -, -, hcl8, -, -, -, -⟩ := hmodel
      let i := nodeOf j
      let n : G := ((w i : ↥L) : G)
      have hconjA : MulAut.conj (w i) ∈
          Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) := by
        let f : ↥(ggGamma L hBsN).range → ↥(ggGamma L hBsN).range :=
          fun a => (hcl8 i a).choose
        have hf : ∀ a : ↥(ggGamma L hBsN).range,
            (f a : MulAut ↥L) = MulAut.conj (w i) * (a : MulAut ↥L) *
              (MulAut.conj (w i))⁻¹ :=
          fun a => ((hcl8 i a).choose_spec.1).symm
        have hfinj : Function.Injective f := by
          intro a a' haa
          have h3 : (f a : MulAut ↥L) = (f a' : MulAut ↥L) := congrArg Subtype.val haa
          rw [hf a, hf a'] at h3
          exact Subtype.ext (mul_left_cancel (mul_right_cancel h3))
        have hsurj := Finite.surjective_of_injective hfinj
        rw [Subgroup.mem_normalizer_iff]
        intro bb
        constructor
        · intro hb
          have hmem : (f ⟨bb, hb⟩ : MulAut ↥L) ∈ (ggGamma L hBsN).range := (f ⟨bb, hb⟩).2
          rwa [hf ⟨bb, hb⟩] at hmem
        · intro hb
          obtain ⟨a, ha⟩ := hsurj
            (⟨MulAut.conj (w i) * bb * (MulAut.conj (w i))⁻¹, hb⟩ : ↥(ggGamma L hBsN).range)
          have h1 : (a : MulAut ↥L) = bb := by
            have h2 : (f a : MulAut ↥L) =
                MulAut.conj (w i) * bb * (MulAut.conj (w i))⁻¹ := congrArg Subtype.val ha
            rw [hf a] at h2
            exact mul_left_cancel (mul_right_cancel h2)
          exact h1 ▸ a.2
      have hnN : n ∈ Subgroup.normalizer (Bs : Set G) := by
        have hconjA' : MulAut.conj (⟨n, (w i).2⟩ : ↥L) ∈
            Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) := by
          have he : (⟨n, (w i).2⟩ : ↥L) = w i := Subtype.ext rfl
          rwa [he]
        exact GGE6Dep.mem_normalizer_of_conj_mem_normalizer_range hp hBsN hBs
          hcfg.bstar_inf_centralizer_L hZ hBsL (w i).2 hconjA'
      refine ⟨ggConjAut Bs hnN,
        ggConjAut_mem_ggAutomizer (H := L) (g := n) (w i).2 hnN, ?_⟩
      refine transfer hBsN hBsL hLx hxBs ι hι5 hιL Φ hιΦ (w i).2 hnN
        (gensL_apply_five j) (closureL_fix_x (Submonoid.subset_closure ⟨j, rfl⟩)) ?_
      intro h hhL
      have hv : (ι (Additive.ofMul h)) 5 = 0 := (hιL h).mp hhL
      obtain ⟨b, hb1, hb2⟩ := hcl8 i ((ggGamma L hBsN).rangeRestrict h)
      have hrel : (↑((ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnN h)) : MulAut ↥L) =
          MulAut.conj (w i) * (↑((ggGamma L hBsN).rangeRestrict h) : MulAut ↥L) *
            (MulAut.conj (w i))⁻¹ := by
        have h1 : ggConjAut Bs hnN h =
            (⟨n * (h : G) * n⁻¹, (Subgroup.mem_normalizer_iff.mp hnN h).mp h.2⟩ : ↥Bs) :=
          Subtype.ext (ggConjAut_apply Bs hnN h)
        rw [h1]
        simp only [MonoidHom.coe_rangeRestrict]
        exact ggGamma_conj L hBsN (w i) h _
      have hb1' : (b : MulAut ↥L) = MulAut.conj (w i) *
          (↑((ggGamma L hBsN).rangeRestrict h) : MulAut ↥L) * (MulAut.conj (w i))⁻¹ :=
        hb1.symm
      have hbeq : (ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnN h) = b :=
        Subtype.ext (hrel.trans hb1'.symm)
      exact (coordE_gensL j (ι (Additive.ofMul h)) hv).trans
        ((congrArg (TableBExc.E6Three.adRefl .E6 3 i) (hιΦ h hv)).trans
          (hb2.symm.trans (by rw [hbeq])))
    | one => exact ⟨1, one_mem _, ActsAs.one ι⟩
    | mul g h hg hh ihg ihh =>
      obtain ⟨φ, hφ, hφg⟩ := ihg
      obtain ⟨ψ, hψ, hψh⟩ := ihh
      exact ⟨φ * ψ, mul_mem hφ hψ, hφg.mul hψh⟩

end E6Dep

end CFSG.StandardType

end
