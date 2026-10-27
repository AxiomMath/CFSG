module

public import CFSG.Quasithin.EmptyFaithful.Gap6R0G

public section

namespace CFSG.Quasithin

namespace LRed12

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.Gap6
open scoped commutatorElement

variable {V : Type*} [CommGroup V] [Finite V] {X : Subgroup (MulAut V)}

theorem hyperplane_facts (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 X = ⊥) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hrk : rk A = 2)
    {B : Subgroup (MulAut V)} (hBA : B ≤ A) (hBcard : Nat.card A = 2 * Nat.card B)
    (hD : ⁅pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V)), A⁆ ≠ ⊥) :
    fixV (fittingOf (Jhat X)) ⊓ fixV B = fixV (fittingOf (Jhat X)) ⊓ fixV A ∧
      rk ↥(commV (fittingOf (Jhat X)) ⊓ fixV A) < rk ↥(commV (fittingOf (Jhat X)) ⊓ fixV B) := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  have hAJ : A ≤ Jhat X := fun a ha => le_Jhat hA ha
  have hJX : Jhat X ≤ X := Jhat_le X
  have hAX : A ≤ X := hAJ.trans hJX
  have hBX : B ≤ X := hBA.trans hAX
  have hAel := hA2.isElemAbelian2
  set F : Subgroup (MulAut V) := fittingOf (Jhat X) with hFdef
  obtain ⟨hsup, hinf⟩ := commV_sup_fixV hV hO2
  have hV₀ : ∀ g ∈ X, ∀ v ∈ commV F, g v ∈ commV F := fun g hg v hv => apply_mem_commV_F hg hv
  have hC : ∀ g ∈ X, ∀ v ∈ fixV F, g v ∈ fixV F := fun g hg v hv => apply_mem_fixV_F hg hv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 (pCoreOf 3 X) := pCoreOf_isPGroup 3 X
  set Q : Subgroup (MulAut V) := pCoreOf 3 X ⊓ Subgroup.centralizer (B : Set (MulAut V)) with hQdef
  have hD3 : ⁅pCoreOf 3 X, A⁆ ≠ ⊥ := fun h =>
    hD (le_bot_iff.mp (h ▸ Subgroup.commutator_mono inf_le_left le_rfl))
  have h13 := D2_13 hV hr hA (p := 3) (by norm_num) rfl hD3
  obtain ⟨-, hhyp⟩ := h13.2.2.2.2 (by omega)
  obtain ⟨hDcard, -, hdir, -⟩ := hhyp B hBA hBcard _ rfl hD
  have hDF : ⁅Q, A⁆ ≤ F := comm_pCore_le_fitting hAJ inf_le_left
  have hα : fixV F ⊓ fixV B ≤ fixV A :=
    inf_fixV_le_of_direct_sum hV (by rw [hDcard]; exact ⟨1, rfl⟩) (fixV_anti hDF) hdir
  have hB2 : IsPGroup 2 B := hAel.isPGroup.to_le hBA
  have hQp : IsPGroup 3 Q := hPp.to_le inf_le_left
  have hQc : ∀ q ∈ Q, ∀ b ∈ B, q * b = b * q := fun q hq b hb =>
    ((Subgroup.mem_centralizer_iff.mp hq.2) b hb).symm
  have hPn : ∀ x ∈ X, ∀ g ∈ pCoreOf 3 X, x * g * x⁻¹ ∈ pCoreOf 3 X := fun x hx g hg =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 3 X hx) g).mp hg
  have hAQ : ∀ a ∈ A, ∀ z ∈ Q, a * z * a⁻¹ ∈ Q := by
    intro a ha z hz
    refine ⟨hPn a (hAX ha) z hz.1, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
    have hab : Commute b a := hAel.1 b (hBA hb) a ha
    have hzb : b * z = z * b := (Subgroup.mem_centralizer_iff.mp hz.2) b hb
    calc b * (a * z * a⁻¹) = (b * a) * z * a⁻¹ := by group
      _ = a * b * z * a⁻¹ := by rw [hab.eq]
      _ = a * (b * z) * a⁻¹ := by group
      _ = a * (z * b) * a⁻¹ := by rw [hzb]
      _ = a * z * (b * a⁻¹) := by group
      _ = a * z * (a⁻¹ * b) := by rw [hab.inv_right.eq]
      _ = a * z * a⁻¹ * b := by group
  have hne : ∃ y ∈ Q, ∃ t ∈ A, t * y ≠ y * t := commutator_ne_bot_iff.mp hD
  have hβ : commSub (fixV B) A ≠ ⊥ := commSub_fixV_ne_bot hV (by norm_num) hQp hB2 hQc hAQ hne
  have hfixAB : fixV A ≤ fixV B := fixV_anti hBA
  have hAnotB : ¬ fixV B ≤ fixV A := fun h => hβ (commSub_eq_bot_iff.mpr h)
  have hlt : rk (fixV A) < rk (fixV B) := by
    by_contra hge
    push Not at hge
    exact hAnotB (eq_of_le_of_rk_le hV hfixAB hge).symm.le
  have E2 : rk ↥(fixV A) = rk ↥(commV F ⊓ fixV A) + rk ↥(fixV F ⊓ fixV A) :=
    rk_fixV_split hsup hinf (fun g hg => hV₀ g (hAX hg)) (fun g hg => hC g (hAX hg))
  have E2B : rk ↥(fixV B) = rk ↥(commV F ⊓ fixV B) + rk ↥(fixV F ⊓ fixV B) :=
    rk_fixV_split hsup hinf (fun g hg => hV₀ g (hBX hg)) (fun g hg => hC g (hBX hg))
  have hCeq : fixV F ⊓ fixV B = fixV F ⊓ fixV A :=
    le_antisymm (le_inf inf_le_left hα) (inf_le_inf_left _ hfixAB)
  refine ⟨hCeq, ?_⟩
  rw [hCeq] at E2B
  omega

theorem exc_rank_bounds (hV : ∀ v : V, v ^ 2 = 1) (hO2 : pCoreOf 2 X = ⊥)
    {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hrk : rk A = 2)
    (hμ : rk ↥(commV (fittingOf (Jhat X))) =
      rk ↥(commV (fittingOf (Jhat X)) ⊓ fixV A) + 3)
    (hk : rk ↥(fixV (fittingOf (Jhat X))) = rk ↥(fixV (fittingOf (Jhat X)) ⊓ fixV A) + 1)
    {x : MulAut V} (hBA : Subgroup.zpowers x ≤ A)
    (hBcard : Nat.card A = 2 * Nat.card (Subgroup.zpowers x))
    (hD : ⁅pCoreOf 3 X ⊓ Subgroup.centralizer ((Subgroup.zpowers x : Subgroup (MulAut V)) :
      Set (MulAut V)), A⁆ ≠ ⊥) :
    rk ↥(commSub (commV (fittingOf (Jhat X))) (Subgroup.zpowers x)) ≤ 2 ∧
      rk ↥(commSub (fixV (fittingOf (Jhat X))) (Subgroup.zpowers x)) = 1 := by
  obtain ⟨hCeq, hlt⟩ := hyperplane_facts hV hO2 hA hrk hBA hBcard hD
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  have hAX : A ≤ X := hA2.le
  have hxX : ∀ y ∈ Subgroup.zpowers x, y ∈ X := fun y hy => hAX (hBA hy)
  have h1 := rk_commSub_add_rk_inf_fixV (g := x) (W := commV (fittingOf (Jhat X)))
    (fun y hy w hw => apply_mem_commV_F (hxX y hy) hw)
  have h2 := rk_commSub_add_rk_inf_fixV (g := x) (W := fixV (fittingOf (Jhat X)))
    (fun y hy w hw => apply_mem_fixV_F (hxX y hy) hw)
  rw [hCeq] at h2
  constructor
  · omega
  · omega

theorem exists_second_hyperplane {A P : Subgroup (MulAut V)} {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥) (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set (MulAut V)))
    (hfaith : ∀ a ∈ A, (∀ y ∈ P, a * y = y * a) → a = 1)
    {B₁ : Subgroup (MulAut V)} (hB₁A : B₁ ≤ A) (hB₁1 : B₁ ≠ ⊥) :
    ∃ B : Subgroup (MulAut V), B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧ B ≠ B₁ ∧
      ∃ y ∈ P ⊓ Subgroup.centralizer (B : Set (MulAut V)), ∃ a ∈ A, a * y ≠ y * a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial A := (Subgroup.nontrivial_iff_ne_bot A).mpr hA1
  have hAelem : CFSG.IsElementaryAbelian 2 A :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hA.1 a a.2 b b.2)⟩⟩
      exponent_dvd_p :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun a => Subtype.ext (hA.2 a a.2) }
  let _ : MulDistribMulAction A P := MulDistribMulAction.compHom P (conjAut hAP)
  have hodd : ¬ 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hP
    rw [hk]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h
    exact hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_two (Fact.out : p.Prime)).1 this).symm
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := A) (H := P) hodd
  by_contra hcon
  push Not at hcon
  have hsmul : ∀ (b : A) (x : P), (((b • x : P)) : MulAut V) =
      (b : MulAut V) * x * (b : MulAut V)⁻¹ := fun b x => rfl
  have hle : (⨆ (B : Subgroup A) (_ : B.index = 2), CFSG.fixedPointSubgroup B P) ≤
      CFSG.fixedPointSubgroup (B₁.subgroupOf A) P := by
    refine iSup₂_le fun B hB x hx => ?_
    by_cases hBeq : B.map A.subtype = B₁
    · intro a'
      have hmem : (a' : A) ∈ B := by
        have h1 : ((a' : A) : MulAut V) ∈ B.map A.subtype := by
          rw [hBeq]; exact a'.2
        obtain ⟨c, hc, hc'⟩ := h1
        have : c = (a' : A) := Subtype.ext hc'
        rw [← this]; exact hc
      exact hx ⟨(a' : A), hmem⟩
    · have hB' : B.map A.subtype ≤ A := by
        rintro _ ⟨b, -, rfl⟩
        exact b.2
      have hcard : Nat.card A = 2 * Nat.card (B.map A.subtype) := by
        have := B.card_mul_index
        rw [hB] at this
        rw [Subgroup.card_map_of_injective A.subtype_injective]
        omega
      have hxc : (x : MulAut V) ∈ P ⊓ Subgroup.centralizer
          ((B.map A.subtype : Subgroup (MulAut V)) : Set (MulAut V)) := by
        refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr ?_⟩
        rintro _ ⟨b, hb, rfl⟩
        have h1 : b • x = x := hx ⟨b, hb⟩
        have h2 := congrArg (fun z : P => (z : MulAut V)) h1
        simp only [hsmul] at h2
        show (b : MulAut V) * x = x * b
        rw [mul_inv_eq_iff_eq_mul] at h2
        exact h2
      intro a'
      have h3 : ((a' : A) • x : P) = x := by
        apply Subtype.ext
        rw [hsmul]
        exact mul_inv_eq_iff_eq_mul.mpr (hcon _ hB' hcard hBeq x hxc (a' : A) (a' : A).2)
      exact h3
  have hall : ∀ y ∈ P, ∀ b ∈ B₁, b * y = y * b := by
    intro y hyP b hb
    have hy : (⟨y, hyP⟩ : P) ∈ CFSG.fixedPointSubgroup (B₁.subgroupOf A) P :=
      hle (hgen ▸ Subgroup.mem_top _)
    have h1 : (⟨b, hB₁A hb⟩ : A) • (⟨y, hyP⟩ : P) = ⟨y, hyP⟩ :=
      hy ⟨⟨b, hB₁A hb⟩, hb⟩
    have h2 := congrArg (fun z : P => (z : MulAut V)) h1
    simp only [hsmul] at h2
    exact mul_inv_eq_iff_eq_mul.mp h2
  apply hB₁1
  rw [Subgroup.eq_bot_iff_forall]
  intro b hb
  exact hfaith b (hB₁A hb) fun y hy => hall y hy b hb

theorem klein_mem {A : Subgroup (MulAut V)} (hE : IsElemAbelian2 A) (hcard : Nat.card A = 4)
    {b e : MulAut V} (hb : b ∈ A) (he : e ∈ A) (hb1 : b ≠ 1) (he1 : e ≠ 1) (hbe : b ≠ e) :
    ∀ g ∈ A, g = 1 ∨ g = b ∨ g = e ∨ g = b * e := by
  classical
  have hb2 : b * b = 1 := by rw [← pow_two]; exact hE.2 b hb
  have hf1 : b * e ≠ 1 := by
    intro h
    apply hbe
    have h1 : e = b⁻¹ := by
      calc e = b⁻¹ * (b * e) := by group
        _ = b⁻¹ := by rw [h, mul_one]
    rw [h1]
    exact (inv_eq_of_mul_eq_one_right hb2).symm
  have hfb : b * e ≠ b := fun h => he1 (by simpa using h)
  have hfe : b * e ≠ e := fun h => hb1 (by simpa using h)
  have : Fintype A := Fintype.ofFinite A
  let S : Finset A := {1, ⟨b, hb⟩, ⟨e, he⟩, ⟨b * e, A.mul_mem hb he⟩}
  have h1b : (1 : A) ≠ ⟨b, hb⟩ := fun h => hb1 (congrArg Subtype.val h).symm
  have h1e : (1 : A) ≠ ⟨e, he⟩ := fun h => he1 (congrArg Subtype.val h).symm
  have h1f : (1 : A) ≠ ⟨b * e, A.mul_mem hb he⟩ := fun h => hf1 (congrArg Subtype.val h).symm
  have hbe' : (⟨b, hb⟩ : A) ≠ ⟨e, he⟩ := fun h => hbe (congrArg Subtype.val h)
  have hbf : (⟨b, hb⟩ : A) ≠ ⟨b * e, A.mul_mem hb he⟩ := fun h => hfb (congrArg Subtype.val h).symm
  have hef : (⟨e, he⟩ : A) ≠ ⟨b * e, A.mul_mem hb he⟩ := fun h => hfe (congrArg Subtype.val h).symm
  have hS : S.card = 4 := by
    simp only [S]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · simpa using hef
    · simp [hbe', hbf]
    · simp [h1b, h1e, h1f]
  have hSU : S = Finset.univ :=
    Finset.eq_univ_of_card S (by rw [hS, ← Nat.card_eq_fintype_card, hcard])
  intro g hg
  have hgS : (⟨g, hg⟩ : A) ∈ S := hSU ▸ Finset.mem_univ _
  simp only [S, Finset.mem_insert, Finset.mem_singleton] at hgS
  rcases hgS with h | h | h | h
  · exact Or.inl (congrArg Subtype.val h)
  · exact Or.inr (Or.inl (congrArg Subtype.val h))
  · exact Or.inr (Or.inr (Or.inl (congrArg Subtype.val h)))
  · exact Or.inr (Or.inr (Or.inr (congrArg Subtype.val h)))

theorem exc_config (hV : ∀ v : V, v ^ 2 = 1) (hsolv : Group.IsSolvable ↥X)
    (hO2 : pCoreOf 2 X = ⊥) {A : Subgroup (MulAut V)} (hA : A ∈ QhatStar X) (hrk : rk A = 2)
    (hμ : rk ↥(commV (fittingOf (Jhat X))) =
      rk ↥(commV (fittingOf (Jhat X)) ⊓ fixV A) + 3)
    (hk : rk ↥(fixV (fittingOf (Jhat X))) = rk ↥(fixV (fittingOf (Jhat X)) ⊓ fixV A) + 1) :
    ∃ b e : MulAut V, b ∈ A ∧ e ∈ A ∧ b ≠ 1 ∧ e ≠ 1 ∧ b ≠ e ∧ b ^ 2 = 1 ∧ e ^ 2 = 1 ∧
      b * e = e * b ∧ (∀ g ∈ A, g = 1 ∨ g = b ∨ g = e ∨ g = b * e) ∧
      (∃ y ∈ pCoreOf 3 X ⊓ Subgroup.centralizer ({b} : Set (MulAut V)), ∃ a ∈ A, a * y ≠ y * a) ∧
      rk ↥(commSub (commV (fittingOf (Jhat X))) (Subgroup.zpowers b)) ≤ 2 ∧
      rk ↥(commSub (commV (fittingOf (Jhat X))) (Subgroup.zpowers e)) ≤ 2 ∧
      rk ↥(commSub (fixV (fittingOf (Jhat X))) (Subgroup.zpowers b)) = 1 := by
  obtain ⟨r, hr, hr2, ⟨⟨hA2, hAr⟩, hAk⟩, hmin⟩ := QhatStar_spec hA
  have hAel := hA2.isElemAbelian2
  have hAX : A ≤ X := hA2.le
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard4 : Nat.card A = 4 := by
    rw [card_eq_two_pow_of_isPGroup hAel.isPGroup, hrk]; norm_num
  have hfaith3 := faithful_pCore_three_of_qhatStar hV hsolv hO2 hA (by omega)
  have hPp : IsPGroup 3 (pCoreOf 3 X) := pCoreOf_isPGroup 3 X
  have hAP : A ≤ Subgroup.normalizer (pCoreOf 3 X : Set (MulAut V)) := fun a ha =>
    le_normalizer_pCoreOf 3 X (hAX ha)
  have hact : ∃ y ∈ pCoreOf 3 X, ∃ a ∈ A, a * y ≠ y * a := by
    obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one (H := A)).mp hA2.ne_bot
    by_contra hcon
    push Not at hcon
    exact ha1 (Subtype.ext (hfaith3 a a.2 fun y hy => hcon y hy a a.2))
  obtain ⟨B₁, hB₁A, hB₁card, y₁, hy₁, a₁, ha₁A, hne₁⟩ :=
    exists_hyperplane_commutator_ne_bot (p := 3) (by norm_num) hAel hA2.ne_bot hPp hAP hact
  have hB₁card2 : Nat.card B₁ = 2 := by omega
  have hB₁el : IsElemAbelian2 B₁ :=
    ⟨fun a ha b hb => hAel.1 a (hB₁A ha) b (hB₁A hb), fun a ha => hAel.2 a (hB₁A ha)⟩
  obtain ⟨b, hbB, hb1, hb2, hbgen⟩ := exists_involution_gen hB₁el hB₁card2
  have hB₁1 : B₁ ≠ ⊥ := fun h => by rw [h, Subgroup.card_bot] at hB₁card2; omega
  obtain ⟨B₂, hB₂A, hB₂card, hB₂ne, y₂, hy₂, a₂, ha₂A, hne₂⟩ :=
    exists_second_hyperplane (p := 3) (by norm_num) hAel hA2.ne_bot hPp hAP hfaith3 hB₁A hB₁1
  have hB₂card2 : Nat.card B₂ = 2 := by omega
  have hB₂el : IsElemAbelian2 B₂ :=
    ⟨fun a ha b hb => hAel.1 a (hB₂A ha) b (hB₂A hb), fun a ha => hAel.2 a (hB₂A ha)⟩
  obtain ⟨e, heB, he1, he2, hegen⟩ := exists_involution_gen hB₂el hB₂card2
  have hbA : b ∈ A := hB₁A hbB
  have heA : e ∈ A := hB₂A heB
  have hbe : b ≠ e := by
    intro h
    apply hB₂ne
    rw [← hegen, ← h, hbgen]
  have hbeC : b * e = e * b := hAel.1 b hbA e heA
  refine ⟨b, e, hbA, heA, hb1, he1, hbe, hb2, he2, hbeC, klein_mem hAel hcard4 hbA heA hb1 he1 hbe,
    ⟨y₁, ⟨hy₁.1, ?_⟩, a₁, ha₁A, hne₁⟩, ?_⟩
  · exact Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB) hy₁.2
  ·
    have hD₁ : ⁅pCoreOf 3 X ⊓ Subgroup.centralizer
        ((Subgroup.zpowers b : Subgroup (MulAut V)) : Set (MulAut V)), A⁆ ≠ ⊥ := by
      rw [hbgen]
      exact commutator_ne_bot_iff.mpr ⟨y₁, hy₁, a₁, ha₁A, hne₁⟩
    have hD₂ : ⁅pCoreOf 3 X ⊓ Subgroup.centralizer
        ((Subgroup.zpowers e : Subgroup (MulAut V)) : Set (MulAut V)), A⁆ ≠ ⊥ := by
      rw [hegen]
      exact commutator_ne_bot_iff.mpr ⟨y₂, hy₂, a₂, ha₂A, hne₂⟩
    have h1 := exc_rank_bounds hV hO2 hA hrk hμ hk (x := b) (by rw [hbgen]; exact hB₁A)
      (by rw [hbgen]; exact hB₁card) hD₁
    have h2 := exc_rank_bounds hV hO2 hA hrk hμ hk (x := e) (by rw [hegen]; exact hB₂A)
      (by rw [hegen]; exact hB₂card) hD₂
    exact ⟨h1.1, h2.1, h1.2⟩

end LRed12

end CFSG.Quasithin
