module

public import CFSG.LocalAnalysis.StandardType.GGNbrLang
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiag
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldCyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem exists_normal_subgroup_of_raw {R : Type} [Group R] {I : Set (MulAut R)}
    (hmul : ∀ φ ∈ I, ∀ ψ ∈ I, φ * ψ ∈ I) (hinv : ∀ φ ∈ I, φ⁻¹ ∈ I)
    (hinn : ∀ r : R, MulAut.conj r ∈ I) (hnorm : GGInndiagNormal R I) :
    ∃ N : Subgroup (MulAut R), (N : Set (MulAut R)) = I ∧ N.Normal := by
  let N : Subgroup (MulAut R) :=
    { carrier := I
      mul_mem' := fun {a b} ha hb => hmul a ha b hb
      one_mem' := by simpa using hinn 1
      inv_mem' := fun {a} ha => hinv a ha }
  refine ⟨N, rfl, ⟨fun n hn g => ?_⟩⟩
  have hle : ggInndiag R I ≤ N := by
    refine sup_le ?_ ?_
    · rintro _ ⟨r, rfl⟩
      exact hinn r
    · exact (Subgroup.closure_le N).2 fun φ hφ => hφ
  exact hle (hnorm g n hn)

theorem exists_index_prime_of_raw_aut {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hsimple : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hraw : GGRawInnField p R I F) (hnorm : GGInndiagNormal R I)
    (hcyc : IsCyclic (Subgroup.closure F)) (ρ : ↥Bs →* MulAut R)
    (hρ : ∀ b : ↥Bs, ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ρ b = u * f)
    {b₀ : G} (hb₀ : b₀ ∈ Bs) (hb₀I : ρ ⟨b₀, hb₀⟩ ∉ I) :
    ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
      ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ρ ⟨b, hb⟩ ∈ I := by
  obtain ⟨hmul, hinv, hinn, -⟩ := hraw hsimple hna
  obtain ⟨N, hNI, hNn⟩ := exists_normal_subgroup_of_raw hmul hinv hinn hnorm
  haveI := hNn
  have hmemN : ∀ a : MulAut R, a ∈ N ↔ a ∈ I := fun a => by rw [← hNI]; rfl
  let χ₀ : ↥Bs →* MulAut R ⧸ N := (QuotientGroup.mk' N).comp ρ
  have hΦ : IsCyclic ↥((Subgroup.closure F).map (QuotientGroup.mk' N)) :=
    isCyclic_of_surjective _ ((QuotientGroup.mk' N).subgroupMap_surjective _)
  have hle : χ₀.range ≤ (Subgroup.closure F).map (QuotientGroup.mk' N) := by
    rintro _ ⟨b, rfl⟩
    obtain ⟨u, hu, f, hf, hbuf⟩ := hρ b
    refine ⟨f, hf, ?_⟩
    have hu1 : QuotientGroup.mk' N u = 1 := (QuotientGroup.eq_one_iff u).2 ((hmemN u).2 hu)
    show QuotientGroup.mk' N f = QuotientGroup.mk' N (ρ b)
    rw [hbuf, map_mul, hu1, one_mul]
  haveI : IsCyclic ↥χ₀.range := Subgroup.isCyclic_of_le hle
  have hker : ∀ b : ↥Bs, χ₀.rangeRestrict b = 1 ↔ ρ b ∈ I := fun b => by
    rw [← hmemN, ← QuotientGroup.eq_one_iff, Subtype.ext_iff]
    rfl
  obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ := exists_index_prime_of_hom_cyclic hp hBs
    χ₀.rangeRestrict hb₀ (fun h => hb₀I ((hker _).1 h))
  exact ⟨B₀, hB₀, hcard, hb₀', fun b hb => (hmem b hb).trans (hker ⟨b, hb⟩)⟩

private theorem isCyclic_quotient_of_gen {M : Type*} [Group M] {J S : Subgroup M}
    (hN : (J.subgroupOf S).Normal) (hcyc : ∃ g ∈ S, ∀ s ∈ S, ∃ k : ℤ, g ^ k * s ∈ J) :
    IsCyclic (S ⧸ J.subgroupOf S) := by
  haveI := hN
  obtain ⟨g₀, hg₀, hgen⟩ := hcyc
  refine ⟨⟨(QuotientGroup.mk (⟨g₀, hg₀⟩ : S) : S ⧸ J.subgroupOf S), fun x => ?_⟩⟩
  induction x using QuotientGroup.induction_on with
  | H s =>
    obtain ⟨k, hk⟩ := hgen s s.2
    have h1 : (QuotientGroup.mk ((⟨g₀, hg₀⟩ : S) ^ k * s) : S ⧸ J.subgroupOf S) = 1 := by
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa using hk
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_zpow] at h1
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g₀, hg₀⟩ : S) : S ⧸ J.subgroupOf S) ^ (-k) = _
    rw [zpow_neg]
    exact inv_eq_of_mul_eq_one_right h1

theorem exists_index_prime_of_raw_pcyclic {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {Bs : Subgroup G} (hBs : IsElemAbelian p Bs) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hsimple : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hPC : GGRawPCyclic p R I F) (ρ : ↥Bs →* MulAut R)
    {b₀ : G} (hb₀ : b₀ ∈ Bs) (hb₀I : ρ ⟨b₀, hb₀⟩ ∉ I) :
    ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
      ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ ρ ⟨b, hb⟩ ∈ I := by
  obtain ⟨J, S, hJI, -, hN, hcyc, hpow⟩ := hPC hsimple hna
  haveI := hN
  haveI : IsCyclic (S ⧸ J.subgroupOf S) := isCyclic_quotient_of_gen hN hcyc
  have hmemJ : ∀ a : MulAut R, a ∈ J ↔ a ∈ I := fun a => by rw [← hJI]; rfl
  have hρS : ∀ b : ↥Bs, ρ b ∈ S := fun b => hpow (ρ b) ⟨1, by
    have hb : b ^ p = 1 := Subtype.ext (hBs.2 b b.2)
    rw [pow_one, ← map_pow, hb, map_one]⟩
  let ρ' : ↥Bs →* S := ρ.codRestrict S hρS
  let χ : ↥Bs →* S ⧸ J.subgroupOf S := (QuotientGroup.mk' (J.subgroupOf S)).comp ρ'
  have hker : ∀ b : ↥Bs, χ.rangeRestrict b = 1 ↔ ρ b ∈ I := fun b => by
    rw [← hmemJ, Subtype.ext_iff]
    show QuotientGroup.mk (ρ' b) = (1 : S ⧸ J.subgroupOf S) ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    rfl
  obtain ⟨B₀, hB₀, hcard, hb₀', hmem⟩ := exists_index_prime_of_hom_cyclic hp hBs
    χ.rangeRestrict hb₀ (fun h => hb₀I ((hker _).1 h))
  exact ⟨B₀, hB₀, hcard, hb₀', fun b hb => (hmem b hb).trans (hker ⟨b, hb⟩)⟩

end CFSG.StandardType
