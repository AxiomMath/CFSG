module

public import CFSG.RankThree.PartOne.U5K.Kf.Ident
public import CFSG.RankThree.PartOne.U5E.Hsub

public section

namespace CFSG.RankThree.PartOne.U5E

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.U5K CFSG.RankThree.PartOne.U5K.Kf
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartTwo.Sec4

@[expose] def NormTwoOf {G : Type} [Group G] (p : ℕ) (E N : Subgroup G) {f : ℕ}
    (ρ : ↥N →* MulAut (projSU 5 2 f)) : Set (Subgroup G) :=
  {B | B ≤ E ∧ Nat.card ↥B = p ^ 3 ∧
    ∃ S : Subgroup G, S ≤ N ∧ IsPGroup 2 ↥S ∧
      (∃ (s : G) (hs : s ∈ N), s ∈ S ∧ ρ ⟨s, hs⟩ ≠ 1) ∧ B ≤ Subgroup.normalizer (S : Set G)}

@[expose] def NormTwo {G : Type} [Group G] (p : ℕ) (E : Subgroup G) {f : ℕ}
    (ρ : ↥(Subgroup.normalizer (lieGenerated p E : Set G)) →* MulAut (projSU 5 2 f)) :
    Set (Subgroup G) :=
  NormTwoOf p E (Subgroup.normalizer (lieGenerated p E : Set G)) ρ

abbrev PI (f : ℕ) (hf : 1 ≤ f) : Type :=
  primeFormP (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)

@[expose] noncomputable def EbarOf {G : Type} [Group G] {N : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    (ρ : ↥N →* MulAut (projSU 5 2 f)) (B : Subgroup G) : Subgroup (MulAut (PI f hf)) :=
  (rm N ρ B).map (MulAut.congr (u5Equiv f hf)).toMonoidHom

structure FrameData (p : ℕ) [Fact p.Prime] {f : ℕ} (hf : 1 ≤ f)
    (Eb : Subgroup (MulAut (PI f hf))) where
  Z : ZetaData (u5FieldData f hf) p
  P : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5)
  diag : ∀ x : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5),
    primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) x ∈ Eb →
      (((P⁻¹ * x * P : primeFormUnitary (u5FieldData f hf)
        (idGram (GaloisField 2 (2 * f)) 5)) : GL (Fin 5) (GaloisField 2 (2 * f))) :
          Matrix (Fin 5) (Fin 5) (GaloisField 2 (2 * f))).IsDiag

section Matrix

variable {p : ℕ} [Fact p.Prime] {f : ℕ} {hf : 1 ≤ f}

theorem atil_eq_Hsub_of_normalizes (Z : ZetaData (u5FieldData f hf) p)
    (P : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5))
    {Bb : Subgroup (MulAut (PI f hf))}
    (hD : Bb ≤ primeFormD (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5))
    (hel : IsElementaryAbelian p ↥Bb) (hcard : Nat.card ↥Bb = p ^ 3)
    (hP : ∀ x : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5),
      primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) x ∈ Bb →
        (((P⁻¹ * x * P : primeFormUnitary (u5FieldData f hf)
          (idGram (GaloisField 2 (2 * f)) 5)) : GL (Fin 5) (GaloisField 2 (2 * f))) :
            Matrix (Fin 5) (Fin 5) (GaloisField 2 (2 * f))).IsDiag)
    {S' : Subgroup (MulAut (PI f hf))} (hS'ne : S' ≠ ⊥) (hS'2 : IsPGroup 2 ↥S')
    (hS'n : Bb ≤ Subgroup.normalizer (S' : Set (MulAut (PI f hf)))) :
    ∃ i j : Fin 5, i < j ∧ Z.Atil P Bb = Hsub p i j := by
  classical
  have hfinK := (u5FieldData f hf).finite
  have hcardAtil : Nat.card ↥(Z.Atil P Bb) = p ^ 4 := by
    rw [Z.card_Atil P hel hD hP, hcard]
    ring
  by_cases hco : ∃ i j : Fin 5, i ≠ j ∧ ∀ a : Fin 5 → ZMod p,
      Multiplicative.ofAdd a ∈ Z.Atil P Bb → a i = a j
  · obtain ⟨i, j, hij, hcoin⟩ := hco
    have hle : Z.Atil P Bb ≤ Hsub p i j := by
      intro a ha
      rw [mem_Hsub]
      exact hcoin (Multiplicative.toAdd a) (by simpa using ha)
    have heq : Z.Atil P Bb = Hsub p i j :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardAtil, card_Hsub hij])
    rcases lt_or_gt_of_ne hij with hlt | hgt
    · exact ⟨i, j, hlt, heq⟩
    · exact ⟨j, i, hgt, heq.trans (Hsub_comm i j)⟩
  · exfalso
    refine Z.false_of_distinguished P hD hcardAtil (fun i j hij => ?_) S' hS'ne hS'2 hS'n
    by_contra hno
    push Not at hno
    exact hco ⟨i, j, hij, hno⟩

end Matrix

section Main

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem Ebar_facts (hEin : U5EInndiag) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {f : ℕ} (hf : 1 ≤ f)
    (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f) :
    EbarOf hf (U5Act (lieGenerated p E) e) E ≤
        primeFormD (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) ∧
      IsElementaryAbelian p ↥(EbarOf hf (U5Act (lieGenerated p E) e) E) ∧
      Nat.card ↥(EbarOf hf (U5Act (lieGenerated p E) e) E) = p ^ 4 := by
  classical
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hEcard : Nat.card ↥E = p ^ 4 := by
    obtain ⟨-, -, -, -, -, hc, -⟩ := hout
    exact hc
  set N : Subgroup G := Subgroup.normalizer (lieGenerated p E : Set G) with hN
  set ρ : ↥N →* MulAut (projSU 5 2 f) := U5Act (lieGenerated p E) e with hρ
  have hEN : E ≤ N := E_le_lieNormalizer h15
  have hinjE : ∀ x ∈ E, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1 := fun x hxE hxN hρ1 =>
    (hEin G p A c L E h15 hF hout f hf e x hxN hxE).2 hρ1
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEbcard : Nat.card ↥(rm N ρ E) = p ^ 4 := by
    rw [card_rm hEN (injective_comp_subtype hinjE), hEcard]
  have hEbel : IsElementaryAbelian p ↥(rm N ρ E) := isElementaryAbelian_rm hEel
  have hEbInd : rm N ρ E ≤ U5Inndiag f := by
    intro a ha
    obtain ⟨x, hxN, hxE, rfl⟩ := mem_rm.1 ha
    exact (hEin G p A c L E h15 hF hout f hf e x hxN hxE).1
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨α, hα, rfl⟩
    have hα1 := hEbInd hα
    have hα' : α ∈ (u5FieldFactor f hf).ker := by rwa [U5Inndiag_eq f hf] at hα1
    have hα2 : MulAut.congr (u5Equiv f hf) α ∈ (primeFormFieldFactor (u5FieldData f hf)
        (isPrimeFormGram_one_GL (n := 5) (K := GaloisField 2 (2 * f))) (by norm_num)
        (by omega)).ker := hα'
    rw [ker_primeFormFieldFactor] at hα2
    exact hα2
  · have : IsElementaryAbelian p ↥(rm (Subgroup.normalizer (lieGenerated p E : Set G))
        (U5Act (lieGenerated p E) e) E) := hEbel
    exact IsElementaryAbelian.map (MulAut.congr (u5Equiv f hf)).toMonoidHom
  · unfold EbarOf
    rw [Subgroup.card_map_of_injective (MulAut.congr (u5Equiv f hf)).injective]
    exact hEbcard

theorem exists_frameData (hEin : U5EInndiag) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {f : ℕ} (hf : 1 ≤ f) (hpf : p ∣ 2 ^ f + 1)
    (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f) :
    have : Fact p.Prime := ⟨h15.h12.prime⟩
    Nonempty (FrameData p hf (EbarOf hf (U5Act (lieGenerated p E) e) E)) := by
  have hp := h15.h12.prime
  have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three (by have := h15.h12.three_lt; omega)
    (by have := h15.h12.three_lt; omega)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨hD, hel, hcard⟩ := Ebar_facts hEin h15 hF hout hf e
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot (u5FieldData f hf) hp hpf
  have hfinK := (u5FieldData f hf).finite
  let Z : ZetaData (u5FieldData f hf) p := ⟨ζ, hζ, hpf, hp5⟩
  obtain ⟨P, hP⟩ := Z.exists_diagonalizing hel
    (by rw [hcard]; exact Nat.pow_le_pow_right hp.pos (by norm_num)) hD
  exact ⟨⟨Z, P, hP⟩⟩

omit [Finite G] in
theorem FrameData.coord [Fact p.Prime] {f : ℕ} {hf : 1 ≤ f} {Eb : Subgroup (MulAut (PI f hf))}
    (fd : FrameData p hf Eb) (hel : IsElementaryAbelian p ↥Eb)
    (hD : Eb ≤ primeFormD (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5))
    {α : MulAut (PI f hf)} (hα : α ∈ Eb) : ∃ a : Fin 5 → ZMod p, fd.Z.par fd.P a = α := by
  have hfinK := (u5FieldData f hf).finite
  obtain ⟨a, ha⟩ := fd.Z.le_range_parHom fd.P hel hD fd.diag hα
  exact ⟨Multiplicative.toAdd a, ha⟩

omit [Finite G] in
theorem EbarOf_injOn {N : Subgroup G} {f : ℕ} (hf : 1 ≤ f) {ρ : ↥N →* MulAut (projSU 5 2 f)}
    (hEN : E ≤ N) (hinjE : ∀ x ∈ E, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1) {B B' : Subgroup G}
    (hB : B ≤ E) (hB' : B' ≤ E) (h : EbarOf hf ρ B = EbarOf hf ρ B') : B = B' := by
  have hrm : rm N ρ B = rm N ρ B' :=
    Subgroup.map_injective (MulAut.congr (u5Equiv f hf)).injective h
  exact le_antisymm (le_of_rm_le_rm hB hB' hEN hinjE hrm.le)
    (le_of_rm_le_rm hB' hB hEN hinjE hrm.ge)

theorem atil_eq_Hsub_gen [Fact p.Prime] {N : Subgroup G} {f : ℕ} {hf : 1 ≤ f}
    {ρ : ↥N →* MulAut (projSU 5 2 f)} (hEel : IsElementaryAbelian p ↥E) (hEN : E ≤ N)
    (hinjE : ∀ x ∈ E, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1)
    (hEbD : EbarOf hf ρ E ≤ primeFormD (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5))
    (fd : FrameData p hf (EbarOf hf ρ E)) {B : Subgroup G} (hB : B ∈ NormTwoOf p E N ρ) :
    ∃ i j : Fin 5, i < j ∧ fd.Z.Atil fd.P (EbarOf hf ρ B) = Hsub p i j := by
  classical
  obtain ⟨hBE, hBcard, S, hSN, hS2, ⟨s, hs, hsS, hρs⟩, hBS⟩ := hB
  have hfinK := (u5FieldData f hf).finite
  have hBbEb : EbarOf hf ρ B ≤ EbarOf hf ρ E := Subgroup.map_mono (rm_mono hBE)
  have hBbD : EbarOf hf ρ B ≤
      primeFormD (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) := hBbEb.trans hEbD
  have hBel : IsElementaryAbelian p ↥B := Sec1514Five.isElementaryAbelian_of_le_aux hEel hBE
  have hBbel : IsElementaryAbelian p ↥(EbarOf hf ρ B) := by
    have := isElementaryAbelian_rm (ρ := ρ) (N := N) hBel
    exact IsElementaryAbelian.map (MulAut.congr (u5Equiv f hf)).toMonoidHom
  have hBbcard : Nat.card ↥(EbarOf hf ρ B) = p ^ 3 := by
    rw [EbarOf, Subgroup.card_map_of_injective (MulAut.congr (u5Equiv f hf)).injective,
      card_rm (hBE.trans hEN) (injective_comp_subtype
        (fun x hx hxN hρ1 => hinjE x (hBE hx) hxN hρ1)), hBcard]
  have hBP : ∀ x : primeFormUnitary (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5),
      primeFormConjHom (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5) x ∈
          EbarOf hf ρ B →
        (((fd.P⁻¹ * x * fd.P : primeFormUnitary (u5FieldData f hf)
          (idGram (GaloisField 2 (2 * f)) 5)) : GL (Fin 5) (GaloisField 2 (2 * f))) :
            Matrix (Fin 5) (Fin 5) (GaloisField 2 (2 * f))).IsDiag :=
    fun x hx => fd.diag x (hBbEb hx)
  have hS'2 : IsPGroup 2 ↥((rm N ρ S).map (MulAut.congr (u5Equiv f hf)).toMonoidHom) :=
    ((hS2.comap_subtype).map ρ).map _
  have hS'ne : (rm N ρ S).map (MulAut.congr (u5Equiv f hf)).toMonoidHom ≠ ⊥ := by
    intro hbot
    apply hρs
    have hmem : (MulAut.congr (u5Equiv f hf)) (ρ ⟨s, hs⟩) ∈
        (rm N ρ S).map (MulAut.congr (u5Equiv f hf)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ (mem_rm.2 ⟨s, hs, hsS, rfl⟩)
    rw [hbot, Subgroup.mem_bot] at hmem
    exact (MulAut.congr (u5Equiv f hf)).injective (hmem.trans (map_one _).symm)
  have hS'n : EbarOf hf ρ B ≤
      Subgroup.normalizer (((rm N ρ S).map (MulAut.congr (u5Equiv f hf)).toMonoidHom :
        Subgroup (MulAut (PI f hf))) : Set (MulAut (PI f hf))) :=
    (Subgroup.map_mono (rm_le_normalizer (ρ := ρ) hBS)).trans
      (Subgroup.le_normalizer_map _)
  exact atil_eq_Hsub_of_normalizes fd.Z fd.P hBbD hBbel hBbcard hBP hS'ne hS'2 hS'n

theorem exists_pair_inj_gen [Fact p.Prime] {N : Subgroup G} {f : ℕ} {hf : 1 ≤ f}
    {ρ : ↥N →* MulAut (projSU 5 2 f)} (hEel : IsElementaryAbelian p ↥E) (hEN : E ≤ N)
    (hinjE : ∀ x ∈ E, ∀ hx : x ∈ N, ρ ⟨x, hx⟩ = 1 → x = 1)
    (hEbD : EbarOf hf ρ E ≤ primeFormD (u5FieldData f hf) (idGram (GaloisField 2 (2 * f)) 5))
    (hEbel : IsElementaryAbelian p ↥(EbarOf hf ρ E)) (fd : FrameData p hf (EbarOf hf ρ E)) :
    ∃ ι : Subgroup G → Fin 5 × Fin 5,
      (∀ B ∈ NormTwoOf p E N ρ, (ι B).1 < (ι B).2) ∧
      (∀ B ∈ NormTwoOf p E N ρ, fd.Z.Atil fd.P (EbarOf hf ρ B) = Hsub p (ι B).1 (ι B).2) ∧
      ∀ B ∈ NormTwoOf p E N ρ, ∀ B' ∈ NormTwoOf p E N ρ, ι B = ι B' → B = B' := by
  classical
  have hfinK := (u5FieldData f hf).finite
  have hEbrange : EbarOf hf ρ E ≤ (fd.Z.parHom fd.P).range :=
    fd.Z.le_range_parHom fd.P hEbel hEbD fd.diag
  have key' : ∀ B : Subgroup G, B ∈ NormTwoOf p E N ρ → ∃ q : Fin 5 × Fin 5, q.1 < q.2 ∧
      fd.Z.Atil fd.P (EbarOf hf ρ B) = Hsub p q.1 q.2 := fun B hB => by
    obtain ⟨i, j, hij, hAB⟩ := atil_eq_Hsub_gen hEel hEN hinjE hEbD fd hB
    exact ⟨(i, j), hij, hAB⟩
  choose! ι hιlt hιeq using key'
  refine ⟨ι, hιlt, hιeq, ?_⟩
  intro B hB B' hB' hι
  have h1 := hιeq B hB
  have h2 := hιeq B' hB'
  rw [hι] at h1
  have hAtil := h1.trans h2.symm
  have hBle : ∀ B'' ∈ NormTwoOf p E N ρ, EbarOf hf ρ B'' ≤ (fd.Z.parHom fd.P).range :=
    fun B'' hB'' => (Subgroup.map_mono (rm_mono hB''.1)).trans hEbrange
  have hmap : EbarOf hf ρ B = EbarOf hf ρ B' := by
    have e1 := Subgroup.map_comap_eq_self (hBle B hB)
    have e2 := Subgroup.map_comap_eq_self (hBle B' hB')
    rw [← e1, ← e2]
    exact congrArg (Subgroup.map (fd.Z.parHom fd.P)) hAtil
  exact EbarOf_injOn hf hEN hinjE hB.1 hB'.1 hmap

theorem exists_pair_inj (hEin : U5EInndiag) (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) {f : ℕ} (hf : 1 ≤ f)
    (e : ↥(lieGenerated p E) ⧸ Subgroup.center ↥(lieGenerated p E) ≃* projSU 5 2 f)
    [Fact p.Prime] (fd : FrameData p hf (EbarOf hf (U5Act (lieGenerated p E) e) E)) :
    ∃ ι : Subgroup G → Fin 5 × Fin 5,
      (∀ B ∈ NormTwo p E (U5Act (lieGenerated p E) e), (ι B).1 < (ι B).2) ∧
      (∀ B ∈ NormTwo p E (U5Act (lieGenerated p E) e),
        fd.Z.Atil fd.P (EbarOf hf (U5Act (lieGenerated p E) e) B) = Hsub p (ι B).1 (ι B).2) ∧
      ∀ B ∈ NormTwo p E (U5Act (lieGenerated p E) e), ∀ B' ∈ NormTwo p E (U5Act (lieGenerated p E) e),
        ι B = ι B' → B = B' := by
  obtain ⟨hEbD, hEbel', -⟩ := Ebar_facts hEin h15 hF hout hf e
  exact exists_pair_inj_gen h15.h12.E_elem (E_le_lieNormalizer h15)
    (fun x hxE hxN hρ1 => (hEin G p A c L E h15 hF hout f hf e x hxN hxE).2 hρ1) hEbD hEbel' fd

end Main

end CFSG.RankThree.PartOne.U5E
