module

public import CFSG.RankThree.PartOne.KE8F.BaseCase
public import CFSG.RankThree.PartOne.KE8F.E8Lang
public import CFSG.RankThree.PartOne.KE8F.HyperGen

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Pointwise MatrixGroups

set_option linter.unusedSectionVars false


section Comm

theorem mem_of_pow_eq_one_comm {G : Type*} [CommGroup G] [Finite G] {p : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsPGroup p P) (hidx : ¬ p ∣ P.index) {g : G} (hg : g ^ p = 1) :
    g ∈ P := by
  classical
  let S : Sylow p G := hP.toSylow hidx
  have hZ : IsPGroup p (Subgroup.zpowers g) := by
    have h1 : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one hg
    rcases (Nat.dvd_prime Fact.out).1 h1 with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; simp)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; simp)
  obtain ⟨Q, hQ⟩ := hZ.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq G S Q
  have hxS : x • S = S := Sylow.smul_eq_of_normal
  rw [hxS] at hx
  have : g ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers g)
  rw [← hx] at this
  exact this

end Comm

section Torsion

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

@[expose] def torsionC (p : ℕ) (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K) :
    Subgroup (adjointGroup .E8 K) :=
  ((T0tors (iterateFrobenius L ℓ f) p).map (rootDiagUnitHom .E8 L)).comap (psiC F c)

theorem mem_torsionC {F : E8P4Frame0 K L ℓ f} {c y : adjointGroup .E8 K} :
    y ∈ torsionC p F c ↔
      ∃ b ∈ T0tors (iterateFrobenius L ℓ f) p, rootDiagUnit .E8 b = psiC F c y := by
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, h⟩

theorem torsionC_torus (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    {y : adjointGroup .E8 K} (hy : y ∈ torsionC p F c) :
    psiC F c y ∈ twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  obtain ⟨b, hb, h⟩ := mem_torsionC.1 hy
  rw [F.hT, ← h]
  exact ⟨b, hb.1, rfl⟩

theorem torsionC_pow (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    {y : adjointGroup .E8 K} (hy : y ∈ torsionC p F c) : y ^ p = 1 := by
  obtain ⟨b, hb, h⟩ := mem_torsionC.1 hy
  apply psiC_injective F c
  rw [map_pow, ← h, rootDiagUnit_pow, map_one]
  have : b ^ p = 1 := funext fun i => by simpa using hb.2 i
  rw [this, rootDiagUnit_one]

theorem mem_torsionC_of_torus (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    {y : adjointGroup .E8 K}
    (hyT : psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hyp : y ^ p = 1) : y ∈ torsionC p F c := by
  have hT := hyT
  rw [F.hT] at hT
  obtain ⟨b, hb, hby⟩ := hT
  refine ⟨b, Subgroup.mem_inf.2 ⟨hb, fun i => ?_⟩, hby⟩
  have h1 : rootDiagUnit .E8 b ^ p = 1 := by
    have hby' : psiC F c y = rootDiagUnit .E8 b := hby.symm
    rw [← hby', ← map_pow, hyp, map_one]
  have h2 : b ^ p = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← rootDiagUnit_pow, h1, rootDiagUnit_one]
  exact congrFun h2 i

theorem torsionC_comm (F : E8P4Frame0 K L ℓ f) (c : adjointGroup .E8 K)
    {a b : adjointGroup .E8 K} (ha : a ∈ torsionC p F c) (hb : b ∈ torsionC p F c) :
    a * b = b * a := by
  apply psiC_injective F c
  obtain ⟨b₁, -, h₁⟩ := mem_torsionC.1 ha
  obtain ⟨b₂, -, h₂⟩ := mem_torsionC.1 hb
  rw [map_mul, map_mul, ← h₁, ← h₂, ← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b₁ b₂]

theorem not_dvd_card_of_dvd_sq_add_one {q : ℕ} {p : ℕ} (hp : p.Prime)
    (hpf : p ∣ q * q + 1) : ¬ p ∣ q := by
  intro h
  have h1 : p ∣ q * q := Dvd.dvd.mul_right h _
  have := (Nat.dvd_add_right h1).1 hpf
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem torsion_le_range (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp5 : 5 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    {S : Sylow p (adjointGroup .E8 K)} {c : adjointGroup .E8 K}
    (hc : ∀ x ∈ (S : Subgroup (adjointGroup .E8 K)), psiC F c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    (T0tors (iterateFrobenius L ℓ f) p).map (rootDiagUnitHom .E8 L) ≤ (psiC F c).range := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]
    exact iterateFrobenius_def ℓ f x
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hpq : ¬ p ∣ Nat.card K := not_dvd_card_of_dvd_sq_add_one hp hpf
  set φ : ↥(fixedCharTuples e8P4V (iterateFrobenius L ℓ f)) →* ModGL .E8 L :=
    (rootDiagUnitHom .E8 L).comp (fixedCharTuples e8P4V (iterateFrobenius L ℓ f)).subtype with hφ
  have hφinj : Function.Injective φ :=
    (rootDiagUnit_injective (τ := .E8) (K := L)).comp Subtype.val_injective
  set S' : Subgroup ↥(fixedCharTuples e8P4V (iterateFrobenius L ℓ f)) :=
    ((S : Subgroup (adjointGroup .E8 K)).map (psiC F c)).comap φ with hS'
  have hle : (S : Subgroup (adjointGroup .E8 K)).map (psiC F c) ≤ φ.range := by
    rintro _ ⟨x, hx, rfl⟩
    have hT := hc x hx
    rw [F.hT] at hT
    obtain ⟨b, hb, hbx⟩ := hT
    exact ⟨⟨b, hb⟩, hbx⟩
  have hmap : S'.map φ = (S : Subgroup (adjointGroup .E8 K)).map (psiC F c) := by
    rw [hS', Subgroup.map_comap_eq, inf_of_le_right hle]
  have hS'card : Nat.card S' = Nat.card (S : Subgroup (adjointGroup .E8 K)) := by
    rw [← Subgroup.card_map_of_injective hφinj, hmap,
      Subgroup.card_map_of_injective (psiC_injective F c)]
  have hSp : Nat.card (S : Subgroup (adjointGroup .E8 K)) =
      p ^ (Nat.card (adjointGroup .E8 K)).factorization p := Sylow.card_eq_multiplicity S
  have hGcard : Nat.card ↥(fixedCharTuples e8P4V (iterateFrobenius L ℓ f)) =
      (Nat.card K * Nat.card K + 1) ^ 4 := card_T0 hFr hℓq
  have hordp := e8P4_ordProj hp hp5 hpq hpf
  have hn0 : (Nat.card K * Nat.card K + 1) ^ 4 ≠ 0 := by positivity
  have hGfin : Finite ↥(fixedCharTuples e8P4V (iterateFrobenius L ℓ f)) :=
    Nat.finite_of_card_ne_zero (by rw [hGcard]; exact hn0)
  have hS'card' : Nat.card S' = p ^ ((Nat.card K * Nat.card K + 1) ^ 4).factorization p := by
    rw [hS'card, hSp]
    exact hordp
  have hpg : IsPGroup p S' := IsPGroup.of_card hS'card'
  have hidx : ¬ p ∣ S'.index := by
    have h1 := Subgroup.card_mul_index S'
    rw [hGcard, hS'card'] at h1
    have h2 : (Nat.card K * Nat.card K + 1) ^ 4 /
        p ^ ((Nat.card K * Nat.card K + 1) ^ 4).factorization p = S'.index :=
      Nat.div_eq_of_eq_mul_right (pow_pos hp.pos _) h1.symm
    rw [← h2]
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 (Nat.coprime_ordCompl hp hn0)
  rintro _ ⟨b, hb, rfl⟩
  have hg : (⟨b, hb.1⟩ : ↥(fixedCharTuples e8P4V (iterateFrobenius L ℓ f))) ^ p = 1 :=
    Subtype.ext (funext fun i => by simpa using hb.2 i)
  have hmem := mem_of_pow_eq_one_comm hpg hidx hg
  have : φ ⟨b, hb.1⟩ ∈ (S : Subgroup (adjointGroup .E8 K)).map (psiC F c) := by
    rw [← hmap]
    exact ⟨_, hmem, rfl⟩
  obtain ⟨y, -, hy⟩ := this
  exact ⟨y, hy⟩

theorem card_torsionC (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hpf : p ∣ Nat.card K * Nat.card K + 1) (c : adjointGroup .E8 K)
    (hle : (T0tors (iterateFrobenius L ℓ f) p).map (rootDiagUnitHom .E8 L) ≤
      (psiC F c).range) : Nat.card (torsionC p F c) = p ^ 4 := by
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]
    exact iterateFrobenius_def ℓ f x
  have hpℓ : ¬ ℓ ∣ p := not_dvd_char hf hK hp hpf
  have hmap : (torsionC p F c).map (psiC F c) =
      (T0tors (iterateFrobenius L ℓ f) p).map (rootDiagUnitHom .E8 L) := by
    rw [torsionC, Subgroup.map_comap_eq, inf_of_le_right hle]
  rw [← Subgroup.card_map_of_injective (psiC_injective F c), hmap,
    Subgroup.card_map_of_injective (rootDiagUnit_injective (τ := .E8) (K := L)),
    card_T0tors hFr hp hpf hpℓ]

end Torsion

section TorusData

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_torusData (F : E8P4Frame K L ℓ f p) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp5 : 5 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    {Q : Subgroup (adjointGroup .E8 K)} (hQ : ∀ x ∈ Q, x ^ p = 1) :
    ∃ c : adjointGroup .E8 K, Q ≤ torsionC p F.toE8P4Frame0 c ∧
      Nat.card (torsionC p F.toE8P4Frame0 c) = p ^ 4 := by
  have : Fact p.Prime := ⟨hp⟩
  have hQp : IsPGroup p Q := fun x => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hQ x x.2)⟩
  obtain ⟨S, hS⟩ := hQp.exists_le_sylow
  obtain ⟨c, hc⟩ := F.hconj (S : Subgroup (adjointGroup .E8 K)) S.isPGroup'
  have hc' : ∀ x ∈ (S : Subgroup (adjointGroup .E8 K)), psiC F.toE8P4Frame0 c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := fun x hx => by
    rw [psiC_apply]
    exact hc x hx
  have hle := torsion_le_range F.toE8P4Frame0 hf hK hp hp5 hpf hc'
  refine ⟨c, fun x hx => mem_torsionC_of_torus F.toE8P4Frame0 c (hc' x (hS hx)) (hQ x hx), ?_⟩
  exact card_torsionC F.toE8P4Frame0 hf hK hp hpf c hle

omit [Finite K] in
theorem T0tors_le_adjoint (Fr : L →+* L) :
    (T0tors Fr p).map (rootDiagUnitHom .E8 L) ≤ adjointGroup .E8 L := by
  rintro _ ⟨b, -, rfl⟩
  have hle : torusGroup .E8 L ≤ adjointGroup .E8 L :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  exact hle (rootDiagUnit_mem_torusGroup b)

theorem exists_torusData_of_toral (F : E8P4Frame0 K L ℓ f) [IsAlgClosure K L] (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p)
    (hpf : p ∣ Nat.card K * Nat.card K + 1) {Q : Subgroup (adjointGroup .E8 K)}
    (hQ : ∀ x ∈ Q, x ^ p = 1) (c : adjointGroup .E8 K)
    (hc : ∀ x ∈ Q, psiC F c x ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    Q ≤ torsionC p F c ∧ Nat.card (torsionC p F c) = p ^ 4 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hFr : ∀ x, iterateFrobenius L ℓ f x = x ^ Nat.card K := fun x => by
    rw [hK]
    exact iterateFrobenius_def ℓ f x
  have hℓq : ℓ ∣ Nat.card K := by
    rw [hK]
    exact dvd_pow_self _ (by omega)
  have hpℓ : ¬ ℓ ∣ p := not_dvd_char hf hK hp hpf
  set Pt : Subgroup (ModGL .E8 L) :=
    (T0tors (iterateFrobenius L ℓ f) p).map (rootDiagUnitHom .E8 L) with hPt
  have hinj : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
  have hPtcard : Nat.card Pt = p ^ 4 := by
    rw [hPt, Subgroup.card_map_of_injective hinj]
    exact card_T0tors hFr hp hpf hpℓ
  have hPtfin : Finite Pt := Nat.finite_of_card_ne_zero (by rw [hPtcard]; positivity)
  set P' : Subgroup (ModGL .E8 L) := Pt.map (MulAut.conj F.g0).toMonoidHom with hP'
  have hP'fin : Finite P' :=
    Finite.of_surjective ((MulAut.conj F.g0).toMonoidHom.subgroupMap Pt)
      ((MulAut.conj F.g0).toMonoidHom.subgroupMap_surjective Pt)
  have hP'adj : P' ≤ adjointGroup .E8 L := by
    rintro _ ⟨z, hz, rfl⟩
    exact mul_mem (mul_mem F.hg0C (T0tors_le_adjoint _ hz)) (inv_mem F.hg0C)
  have hPtT : ∀ z ∈ Pt, F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z * F.n⁻¹ = z := by
    rintro _ ⟨b, hb, rfl⟩
    have hbT : rootDiagUnit .E8 b ∈
        twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
      rw [F.hT]
      exact ⟨b, hb.1, rfl⟩
    exact (mem_twistedTorusOf.1 hbT).2
  have hP'fix : ∀ w ∈ P', Units.map (entrywiseHom (iterateFrobenius L ℓ f)) w = w := by
    rintro _ ⟨z, hz, rfl⟩
    change Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (F.g0 * z * F.g0⁻¹) =
      F.g0 * z * F.g0⁻¹
    rw [map_mul, map_mul, map_inv, F.hg0]
    calc F.g0 * F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z * (F.g0 * F.n)⁻¹
        = F.g0 * (F.n * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) z * F.n⁻¹) *
            F.g0⁻¹ := by group
      _ = F.g0 * z * F.g0⁻¹ := by rw [hPtT z hz]
  have hP'p : IsPGroup p P' := by
    intro w
    obtain ⟨z, hz, hzw⟩ := w.2
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← hzw]
    obtain ⟨b, hb, rfl⟩ := hz
    have h1 : rootDiagUnit .E8 b ^ p = 1 := by
      have : b ^ p = 1 := funext fun i => by simpa using hb.2 i
      rw [rootDiagUnit_pow, this, rootDiagUnit_one]
    change (F.g0 * rootDiagUnit .E8 b * F.g0⁻¹) ^ p = 1
    rw [conj_pow, h1]
    group
  have hle := fixed_pgroup_le_range K hK L hp hp3 P' hP'adj hP'fix hP'p
  have hPtle : Pt ≤ (psiC F c).range := by
    intro z hz
    have hzP' : F.g0 * z * F.g0⁻¹ ∈ P' := Subgroup.mem_map_of_mem _ hz
    obtain ⟨y, hy⟩ := hle hzP'
    refine ⟨c⁻¹ * y * c, ?_⟩
    rw [psiC_apply, show c * (c⁻¹ * y * c) * c⁻¹ = y by group, hy]
    group
  refine ⟨fun x hx => mem_torsionC_of_torus F c (hc x hx) (hQ x hx), ?_⟩
  exact card_torsionC F hf hK hp hpf c hPtle

theorem V_le_torus_gen (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : 2 < p) (hgen : StabGen L (iterateFrobenius L ℓ f) p)
    (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (c : adjointGroup .E8 K) (hcard : Nat.card (torsionC p F c) = p ^ 4)
    {X : Subgroup (adjointGroup .E8 K)} (hXA : X ≤ torsionC p F c)
    {V : Subgroup (adjointGroup .E8 K)}
    (hVX : V ≤ Subgroup.centralizer (X : Set (adjointGroup .E8 K)))
    (hVn : ∀ d ∈ Subgroup.centralizer (X : Set (adjointGroup .E8 K)), ∀ v ∈ V, d * v * d⁻¹ ∈ V)
    (hVs : Group.IsSolvable V) (hVp : ¬ p ∣ Nat.card V) :
    ∀ v ∈ V, psiC F c v ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  have : Fact p.Prime := ⟨hp⟩
  have hEA : IsElementaryAbelian p (torsionC p F c) :=
    { is_comm := ⟨fun a b => Subtype.ext (torsionC_comm F c a.2 b.2)⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun a =>
        Subtype.ext (by simpa using torsionC_pow F c a.2) }
  have hle := le_of_base_hyperplanes (p := p) (A := torsionC p F c)
    (T := (twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))).comap
      (psiC F c)) hcard
    (fun Y hYA hYcard V' hV'D hV'n hV's _ => fun v hv =>
      base_case_gen F hf hK hp hp2 hgen hpf c (fun y hy => torsionC_torus F c (hYA hy))
        (fun y hy => torsionC_pow F c (hYA hy)) hYcard hV'D hV'n hV's v hv)
    hXA hVX hVn hVs hVp
  exact fun v hv => hle hv

theorem V_le_torus (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (c : adjointGroup .E8 K) (hcard : Nat.card (torsionC p F c) = p ^ 4)
    {X : Subgroup (adjointGroup .E8 K)} (hXA : X ≤ torsionC p F c)
    {V : Subgroup (adjointGroup .E8 K)}
    (hVX : V ≤ Subgroup.centralizer (X : Set (adjointGroup .E8 K)))
    (hVn : ∀ d ∈ Subgroup.centralizer (X : Set (adjointGroup .E8 K)), ∀ v ∈ V, d * v * d⁻¹ ∈ V)
    (hVs : Group.IsSolvable V) (hVp : ¬ p ∣ Nat.card V) :
    ∀ v ∈ V, psiC F c v ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
  V_le_torus_gen F hf hK hp (by omega)
    (stabGen_of_not_dvd_weyl hp hp10 (not_dvd_char hf hK hp hpf)) hpf c hcard hXA hVX hVn hVs hVp

end TorusData

section HV

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem twistedTorus_comm (F : E8P4Frame0 K L ℓ f) {a b : ModGL .E8 L}
    (ha : a ∈ twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    (hb : b ∈ twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f)))) :
    a * b = b * a := by
  rw [F.hT] at ha hb
  obtain ⟨b₁, -, rfl⟩ := ha
  obtain ⟨b₂, -, rfl⟩ := hb
  change rootDiagUnit .E8 b₁ * rootDiagUnit .E8 b₂ = rootDiagUnit .E8 b₂ * rootDiagUnit .E8 b₁
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm b₁ b₂]

theorem V_centralizer_le_torus (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : 2 < p) (hgen : StabGen L (iterateFrobenius L ℓ f) p)
    (hpf : p ∣ Nat.card K * Nat.card K + 1) {x : adjointGroup .E8 K} (c : adjointGroup .E8 K)
    (hxA : x ∈ torsionC p F c) (hcard : Nat.card (torsionC p F c) = p ^ 4)
    (V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))) (hVn : V.Normal)
    (hVs : Group.IsSolvable V) (hVp : ¬ p ∣ Nat.card V) :
    ∀ v : V, psiC F c (((v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) :
      adjointGroup .E8 K)) ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
  classical
  have hQA : Subgroup.zpowers x ≤ torsionC p F c := (Subgroup.zpowers_le).2 hxA
  have hcommx : ∀ d ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)),
      ∀ h ∈ Subgroup.zpowers x, h * d = d * h := by
    intro d hd h hh
    have hxd : x * d = d * x := (Subgroup.mem_centralizer_singleton_iff.1 hd).symm
    obtain ⟨k, rfl⟩ := hh
    exact ((Commute.zpow_left (show Commute x d from hxd) k)).eq
  have hVX : V.map (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype ≤
      Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (adjointGroup .E8 K)) :
        Set (adjointGroup .E8 K)) := by
    rintro _ ⟨v, hv, rfl⟩
    exact Subgroup.mem_centralizer_iff.2 (hcommx v v.2)
  have hVn' : ∀ d ∈ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (adjointGroup .E8 K)) :
      Set (adjointGroup .E8 K)), ∀ v ∈ V.map
        (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype, d * v * d⁻¹ ∈ V.map
          (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype := by
    intro d hd v hv
    obtain ⟨v', hv', rfl⟩ := hv
    have hdD : d ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) :=
      Subgroup.mem_centralizer_singleton_iff.2
        (Subgroup.mem_centralizer_iff.1 hd x (Subgroup.mem_zpowers x)).symm
    exact ⟨⟨d, hdD⟩ * v' * ⟨d, hdD⟩⁻¹, hVn.conj_mem v' hv' ⟨d, hdD⟩, rfl⟩
  have hVs' : Group.IsSolvable (V.map
      (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype) := by
    have e := Subgroup.equivMapOfInjective V
      (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype
      (Subgroup.subtype_injective _)
    exact Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) (MulEquiv.injective _)
  have hVp' : ¬ p ∣ Nat.card (V.map
      (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype) := by
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have hle := V_le_torus_gen F hf hK hp hp2 hgen hpf c hcard hQA hVX hVn' hVs' hVp'
  exact fun v => hle _ ⟨v, v.2, rfl⟩

theorem hV_E8 (F : E8P4Frame K L ℓ f p) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1) :
    ∀ x : adjointGroup .E8 K, orderOf x = p →
      ∀ V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))), V.Normal →
        Group.IsSolvable V → ¬ p ∣ Nat.card V →
        (∀ v ∈ V, ∀ w ∈ V, v * w = w * v) ∧ Nat.card {v : V // v ^ 2 = 1} ≤ 16 := by
  classical
  intro x hx V hVn hVs hVp
  have : Fact p.Prime := ⟨hp⟩
  have hFr : ∀ y, iterateFrobenius L ℓ f y = y ^ Nat.card K := fun y => by
    rw [hK]
    exact iterateFrobenius_def ℓ f y
  have hxp : ∀ y ∈ Subgroup.zpowers x, y ^ p = 1 := by
    rintro y ⟨k, rfl⟩
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, ← hx,
      pow_orderOf_eq_one, _root_.one_zpow]
  obtain ⟨c, hQA, hcard⟩ := exists_torusData F hf hK hp (by omega) hpf hxp
  have hVT := V_centralizer_le_torus F.toE8P4Frame0 hf hK hp (by omega)
    (stabGen_of_not_dvd_weyl hp hp10 (not_dvd_char hf hK hp hpf)) hpf c
    (hQA (Subgroup.mem_zpowers x)) hcard V hVn hVs hVp
  refine ⟨fun v hv w hw => ?_, ?_⟩
  · apply Subtype.ext
    apply psiC_injective F.toE8P4Frame0 c
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact twistedTorus_comm F.toE8P4Frame0 (hVT ⟨v, hv⟩) (hVT ⟨w, hw⟩)
  ·
    have hinj : Function.Injective (rootDiagUnitHom .E8 L) := rootDiagUnit_injective
    let φ : V →* (rootDiagUnitHom .E8 L).range :=
      (((psiC F.toE8P4Frame0 c).comp
        (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))).subtype).comp
        V.subtype).codRestrict _ (fun v => by
        have := hVT v
        rw [F.hT] at this
        obtain ⟨b, -, hb⟩ := this
        exact ⟨b, hb⟩)
    let ψ' : V →* (Fin Tag.E8.rank → Lˣ) :=
      (MonoidHom.ofInjective hinj).symm.toMonoidHom.comp φ
    have hψ'inj : Function.Injective ψ' := by
      intro a b hab
      have h1 := (MonoidHom.ofInjective hinj).symm.injective hab
      have h2 : psiC F.toE8P4Frame0 c (((a : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) :
          adjointGroup .E8 K)) = psiC F.toE8P4Frame0 c (((b : Subgroup.centralizer
            ({x} : Set (adjointGroup .E8 K))) : adjointGroup .E8 K)) :=
        congrArg Subtype.val h1
      exact Subtype.ext (Subtype.ext (psiC_injective F.toE8P4Frame0 c h2))
    have hψ'T : ∀ v, ψ' v ∈ fixedCharTuples e8P4V (iterateFrobenius L ℓ f) := by
      intro v
      have h1 : rootDiagUnitHom .E8 L (ψ' v) = psiC F.toE8P4Frame0 c (((v : Subgroup.centralizer
          ({x} : Set (adjointGroup .E8 K))) : adjointGroup .E8 K)) := by
        have := (MonoidHom.ofInjective hinj).apply_symm_apply (φ v)
        exact congrArg Subtype.val this
      have h2 := hVT v
      rw [F.hT] at h2
      obtain ⟨b, hb, hbv⟩ := h2
      have : b = ψ' v := hinj (hbv.trans h1.symm)
      rw [← this]
      exact hb
    exact card_two_torsion_le_sixteen hFr ψ' hψ'inj hψ'T

theorem hV_odd_of_toral (F : E8P4Frame0 K L ℓ f) (hℓ2 : ℓ = 2) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp2 : 2 < p)
    (hgen : StabGen L (iterateFrobenius L ℓ f) p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    {x : adjointGroup .E8 K} (c : adjointGroup .E8 K) (hxA : x ∈ torsionC p F c)
    (hcard : Nat.card (torsionC p F c) = p ^ 4)
    (V : Subgroup (Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)))) (hVn : V.Normal)
    (hVs : Group.IsSolvable V) (hVp : ¬ p ∣ Nat.card V) : Odd (Nat.card V) := by
  classical
  subst hℓ2
  have hVT := V_centralizer_le_torus F hf hK hp hp2 hgen hpf c hxA hcard V hVn hVs hVp
  by_contra hne
  have h2 : 2 ∣ Nat.card V := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hv2 : v ^ 2 = 1 := by rw [← hv]; exact pow_orderOf_eq_one v
  have hv2' : (((v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) :
      adjointGroup .E8 K)) ^ 2 = 1 := by
    have := congrArg (fun w : V => ((w : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) :
      adjointGroup .E8 K)) hv2
    simpa using this
  have hvT := hVT v
  rw [F.hT] at hvT
  obtain ⟨b, -, hb⟩ := hvT
  have hb0 : rootDiagUnit .E8 b = psiC F c (((v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) :
      adjointGroup .E8 K)) := hb
  have hb' : (rootDiagUnit .E8 b) ^ 2 = 1 := by
    rw [hb0, ← map_pow, hv2', map_one]
  have hb2 : b ^ 2 = 1 := by
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← rootDiagUnit_pow, hb', rootDiagUnit_one]
  have hbi : b = 1 := funext fun i => by
    have hi : (b i) ^ 2 = 1 := by simpa using congrFun hb2 i
    have hu : ((b i : Lˣ) : L) ^ 2 = (1 : L) ^ 2 := by
      rw [← Units.val_pow_eq_pow_val, hi, Units.val_one, one_pow]
    exact Units.ext (by simpa using (CharTwo.sq_inj (R := L)).1 hu)
  have hψ : psiC F c (((v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) :
      adjointGroup .E8 K)) = 1 := by rw [← hb0, hbi, rootDiagUnit_one]
  have hv1 : (((v : Subgroup.centralizer ({x} : Set (adjointGroup .E8 K))) :
      adjointGroup .E8 K)) = 1 := psiC_injective F c (by rw [hψ, map_one])
  have hv1' : v = 1 := Subtype.ext (Subtype.ext hv1)
  rw [hv1', orderOf_one] at hv
  omega

end HV

end CFSG.RankThree.PartOne.KE8F
