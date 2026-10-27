module

public import CFSG.Quasithin.Background.FFC4S3
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique
open scoped commutatorElement

theorem card_sl2_two : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem sl2_noncomm : ∀ x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    (x ^ 2 = 1 ∧ x ≠ 1 ∧ y ^ 3 = 1 ∧ y ≠ 1) → x * y ≠ y * x := by
  decide

theorem sl2_prod_invol : ∀ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    ∃ x y : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), x ^ 2 = 1 ∧ y ^ 2 = 1 ∧ g = x * y := by
  decide

variable {V : Type} [CommGroup V] [Finite V]

theorem card_eq_two_of_sylow {H A : Subgroup (MulAut V)}
    (hH : Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (hA : IsSylowTwoOf A H) : Nat.card A = 2 := by
  obtain ⟨e⟩ := hH
  have h6 : Nat.card H = 6 := by rw [Nat.card_congr e.toEquiv, card_sl2_two]
  have h1 := Subgroup.card_mul_index (A.subgroupOf H)
  have h2 : Nat.card (A.subgroupOf H) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  rw [h2, h6] at h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).1 hA.2.1
  rw [hn] at h1
  have hodd := hA.2.2
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exfalso
      apply hodd
      simp at h1
      omega
    · simpa using hn
  · exfalso
    have h4 : 2 ^ 2 ∣ 2 ^ n * (A.subgroupOf H).index := by
      exact Dvd.dvd.mul_right (pow_dvd_pow 2 hn2) _
    rw [h1] at h4
    omega

theorem s3pair_of_sl2 {G₁ A F : Subgroup (MulAut V)}
    (hG : Nonempty (↥G₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) (hF : Nat.card F = 3)
    (hFle : F ≤ G₁) (hFn : ∀ g ∈ G₁, ∀ f ∈ F, g * f * g⁻¹ ∈ F) (hA : IsSylowTwoOf A G₁) :
    S3Pair F A ∧ G₁ = F ⊔ A := by
  have hA2 := card_eq_two_of_sylow hG hA
  obtain ⟨e⟩ := hG
  have h6 : Nat.card G₁ = 6 := by rw [Nat.card_congr e.toEquiv, card_sl2_two]
  refine ⟨⟨hF, hA2, fun a ha f hf => hFn a (hA.1 ha) f hf, ?_⟩, ?_⟩
  ·
    have hbotA : A ≠ ⊥ := by
      intro hb
      have := Subgroup.card_eq_one.2 hb
      omega
    have hbotF : F ≠ ⊥ := by
      intro hb
      have := Subgroup.card_eq_one.2 hb
      omega
    obtain ⟨x, hx⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbotA
    obtain ⟨y, hy⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbotF
    refine ⟨x, x.2, y, y.2, ?_⟩
    have hx2 : x ^ 2 = 1 := by
      have := pow_card_eq_one' (G := ↥A) (x := x)
      rwa [hA2] at this
    have hy3 : y ^ 3 = 1 := by
      have := pow_card_eq_one' (G := ↥F) (x := y)
      rwa [hF] at this
    let a' : ↥G₁ := ⟨x, hA.1 x.2⟩
    let f' : ↥G₁ := ⟨y, hFle y.2⟩
    have ha2 : a' ^ 2 = 1 := Subtype.ext (by simpa using congrArg Subtype.val hx2)
    have hf3 : f' ^ 3 = 1 := Subtype.ext (by simpa using congrArg Subtype.val hy3)
    have ha1 : a' ≠ 1 := fun h => hx (Subtype.ext (by simpa [a'] using congrArg Subtype.val h))
    have hf1 : f' ≠ 1 := fun h => hy (Subtype.ext (by simpa [f'] using congrArg Subtype.val h))
    have key := sl2_noncomm (e a') (e f') ⟨by rw [← map_pow, ha2, map_one],
      fun h => ha1 (e.injective (h.trans (map_one e).symm)), by rw [← map_pow, hf3, map_one],
      fun h => hf1 (e.injective (h.trans (map_one e).symm))⟩
    intro hcomm
    apply key
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  ·
    have hle : F ⊔ A ≤ G₁ := sup_le hFle hA.1
    have hd1 : 3 ∣ Nat.card ↥(F ⊔ A) := hF ▸ Subgroup.card_dvd_of_le (le_sup_left : F ≤ F ⊔ A)
    have hd2 : 2 ∣ Nat.card ↥(F ⊔ A) := hA2 ▸ Subgroup.card_dvd_of_le (le_sup_right : A ≤ F ⊔ A)
    have hd3 : Nat.card ↥(F ⊔ A) ∣ 6 := h6 ▸ Subgroup.card_dvd_of_le hle
    have h6' : Nat.card ↥(F ⊔ A) = 6 := by
      have h23 : 6 ∣ Nat.card ↥(F ⊔ A) := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) hd1 hd2
      exact Nat.dvd_antisymm hd3 h23
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm


theorem sl2_eq_iSup_sylow {H : Subgroup (MulAut V)}
    (hH : Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))) :
    H = ⨆ (B : Subgroup (MulAut V)) (_ : IsSylowTwoOf B H), B := by
  obtain ⟨e⟩ := hH
  refine le_antisymm (fun x hx => ?_) (iSup₂_le fun B hB => hB.1)
  have hmem : ∀ w : ↥H, w ^ 2 = 1 → (w : MulAut V) ∈ ⨆ (B : Subgroup (MulAut V))
      (_ : IsSylowTwoOf B H), B := by
    intro w hw2
    have hle : Subgroup.zpowers (w : MulAut V) ≤ H :=
      (Subgroup.zpowers_le).2 w.2
    have hU : IsPGroup 2 ↥(Subgroup.zpowers (w : MulAut V)) := by
      intro y
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 y.2
      refine ⟨1, Subtype.ext ?_⟩
      have h2 : (w : MulAut V) ^ 2 = 1 := by simpa using congrArg Subtype.val hw2
      calc ((y : MulAut V)) ^ 2 ^ 1 = ((w : MulAut V) ^ j) ^ 2 := by rw [← hj]; simp
        _ = ((w : MulAut V) ^ 2) ^ j := by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]; simp
        _ = 1 := by rw [h2, one_zpow]
    obtain ⟨S, hUS, hS⟩ := exists_isSylowTwoOf_of_le hle hU
    have hSle : S ≤ ⨆ (B : Subgroup (MulAut V)) (_ : IsSylowTwoOf B H), B :=
      le_iSup₂ (f := fun (B : Subgroup (MulAut V)) (_ : IsSylowTwoOf B H) => B) S hS
    exact hSle (hUS (Subgroup.mem_zpowers _))
  obtain ⟨u, v, hu, hv, huv⟩ := sl2_prod_invol (e ⟨x, hx⟩)
  have hxuv : (⟨x, hx⟩ : ↥H) = e.symm u * e.symm v := by
    rw [← map_mul, ← huv]; simp
  have hu' : (e.symm u) ^ 2 = 1 := by rw [← map_pow, hu, map_one]
  have hv' : (e.symm v) ^ 2 = 1 := by rw [← map_pow, hv, map_one]
  have h1 := hmem _ hu'
  have h2 := hmem _ hv'
  have : x = ((e.symm u : ↥H) : MulAut V) * ((e.symm v : ↥H) : MulAut V) := by
    simpa using congrArg Subtype.val hxuv
  rw [this]
  exact Subgroup.mul_mem _ h1 h2


structure B58Split (G A G₁ G₂ F : Subgroup (MulAut V)) : Prop where
  A_le : A ≤ G₁
  G₁_le : G₁ ≤ G
  G₂_le : G₂ ≤ G
  sup : G₁ ⊔ G₂ = G
  inf : G₁ ⊓ G₂ = ⊥
  comm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a
  s3 : S3Pair F A
  G₁_eq : G₁ = F ⊔ A
  iso : Nonempty (↥G₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))
  card_comm : Nat.card (commV G₁) = 4
  comm_eq : commV G₁ = commV F
  fix_eq : fixV G₁ = fixV F
  dec_sup : commV G₁ ⊔ fixV G₁ = ⊤
  dec_inf : commV G₁ ⊓ fixV G₁ = ⊥
  triv₁ : ∀ b ∈ G₂, ∀ v ∈ commV G₁, b v = v
  gen₂ : G₂ = ⨆ (B : Subgroup (MulAut V)) (_ : IsFFStarOffender G B ∧ B ≤ G₂), B

theorem b58_split (hV : ∀ v : V, v ^ 2 = 1) {G A : Subgroup (MulAut V)} (hO2 : pCoreOf 2 G = ⊥)
    (hJ : G = ffJ G) (hA : IsFFStarMin G A) (hne : ⁅fittingOf G, A⁆ ≠ ⊥) :
    ∃ G₁ G₂ F : Subgroup (MulAut V), B58Split G A G₁ G₂ F := by
  have hAJ : A ≤ ffJP {B | IsFFStarMin G B} G :=
    le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ {B | IsFFStarMin G B}) =>
      ⨆ (_ : B ≤ G), B) A hA (le_iSup (fun _ : A ≤ G => A) hA.1.1)
  have hFJ : ⁅fittingOfSub G, ffJP {B | IsFFStarMin G B} G⁆ ≠ ⊥ := fun h =>
    hne (le_bot_iff.1 (h ▸ Subgroup.commutator_mono le_rfl hAJ))
  obtain ⟨s, H, h1a, h1b, -, h2b, -, h3a, -, -, h4, -⟩ :=
      CFSG.Quasithin.EmptyFaithfulMultiple.inputB19_holds V hV G hO2 hFJ
  obtain ⟨i₀, hi₀⟩ := (h4 A).1 ⟨hA, hne⟩
  let K : Option (Fin s) → Subgroup (MulAut V) := fun o => o.elim
    (ffJP {B | IsFFStarOffender G B} (G ⊓ Subgroup.centralizer
      ((⁅fittingOfSub G, ffJP {B | IsFFStarMin G B} G⁆ : Subgroup (MulAut V)) : Set (MulAut V)))) H
  have h1b' : IsInnerDirectProduct K (ffJ G) := h1b
  obtain ⟨hKcomm, hKindep, hKsup⟩ := h1b'
  have hKle : ∀ o, K o ≤ G := fun o => by
    have : K o ≤ ⨆ o', K o' := le_iSup K o
    rw [hKsup, ← hJ] at this
    exact this
  have hHG : H i₀ ≤ G := (h1a i₀).1
  set G₂ : Subgroup (MulAut V) := ⨆ (o : Option (Fin s)) (_ : o ≠ some i₀), K o with hG₂
  have hKG₂ : ∀ o, o ≠ some i₀ → K o ≤ G₂ := fun o ho =>
    le_iSup₂ (f := fun (o : Option (Fin s)) (_ : o ≠ some i₀) => K o) o ho
  set F : Subgroup (MulAut V) := oddCoreOfSub (H i₀) with hF
  have hFle : F ≤ H i₀ := Subgroup.map_subtype_le _
  have hFn : ∀ g ∈ H i₀, ∀ f ∈ F, g * f * g⁻¹ ∈ F := by
    intro g hg f hf
    obtain ⟨y, hy, rfl⟩ := hf
    refine ⟨(⟨g, hg⟩ : ↥(H i₀)) * y * (⟨g, hg⟩ : ↥(H i₀))⁻¹,
      (CFSG.oddCore_normal (G := ↥(H i₀))).conj_mem y hy ⟨g, hg⟩, ?_⟩
    simp
  obtain ⟨hs3, hG₁eq⟩ := s3pair_of_sl2 (h1a i₀).2 (h2b i₀) hFle hFn hi₀
  have hcomm : ∀ a ∈ H i₀, ∀ b ∈ G₂, a * b = b * a := by
    intro a ha b hb
    have hle : G₂ ≤ Subgroup.centralizer ({a} : Set (MulAut V)) := by
      refine iSup₂_le fun o ho x hx => ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hKcomm (some i₀) o (Ne.symm ho) y ha x hx
    exact Subgroup.mem_centralizer_iff.1 (hle hb) a (Set.mem_singleton a)
  have hinf : H i₀ ⊓ G₂ = ⊥ := disjoint_iff.1 (hKindep (some i₀))
  have hsup : H i₀ ⊔ G₂ = G := by
    refine le_antisymm (sup_le hHG (iSup₂_le fun o _ => hKle o)) ?_
    rw [hJ, ← hKsup]
    refine iSup_le fun o => ?_
    by_cases ho : o = some i₀
    · subst ho
      exact le_sup_left
    · exact (hKG₂ o ho).trans le_sup_right
  have hoff : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
    have := hA.1.2.2.2 ⊥ bot_le
    rwa [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at this
  have hfle : fixV F ≤ fixV A := hs3.fixV_le_fixV hV hoff
  have hfix : fixV (H i₀) = fixV F := by
    refine le_antisymm (B1.fixV_le_fixV hFle) fun v hv => ?_
    have hle : F ⊔ A ≤ MulAction.stabilizer (MulAut V) v :=
      sup_le (fun f hf => hv f hf) (fun a ha => hfle hv a ha)
    intro x hx
    rw [hG₁eq] at hx
    exact hle hx
  have hcommeq : commV (H i₀) = commV F := ((h3a i₀).1).symm
  have hcardF : Nat.card (commV F) = 4 := hcommeq ▸ (h3a i₀).2
  obtain ⟨hdsup, hdinf⟩ := hs3.decomp hV
  refine ⟨H i₀, G₂, F, ⟨hi₀.1, hHG, iSup₂_le fun o _ => hKle o, hsup, hinf, hcomm, hs3, hG₁eq,
    (h1a i₀).2, (h3a i₀).2, hcommeq, hfix, by rw [hcommeq, hfix]; exact hdsup,
    by rw [hcommeq, hfix]; exact hdinf, ?_, ?_⟩⟩
  · intro b hb v hv
    rw [hcommeq] at hv
    exact hs3.trivial_of_commute hV hcardF
      (fun f hf => (hcomm f (hFle hf) b hb).symm)
      (fun a ha => (hcomm a (hi₀.1 ha) b hb).symm) v hv
  · refine le_antisymm (iSup₂_le fun o ho => ?_) (iSup₂_le fun B hB => hB.2)
    rcases o with _ | i
    ·
      show ffJP _ _ ≤ _
      refine iSup₂_le fun B hB => iSup_le fun hBle => ?_
      have hBK : B ≤ K none :=
        le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ {B | IsFFStarOffender G B}) =>
          ⨆ (_ : B ≤ G ⊓ Subgroup.centralizer
            ((⁅fittingOfSub G, ffJP {B | IsFFStarMin G B} G⁆ : Subgroup (MulAut V)) :
              Set (MulAut V))), B) B hB (le_iSup (fun _ => B) hBle)
      exact le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : IsFFStarOffender G B ∧ B ≤ G₂) => B)
        B ⟨hB, hBK.trans (hKG₂ none (by simp))⟩ le_rfl
    ·
      have hHi : K (some i) = H i := rfl
      have hiG₂ : H i ≤ G₂ := hKG₂ (some i) ho
      show H i ≤ _
      rw [sl2_eq_iSup_sylow (h1a i).2]
      refine iSup₂_le fun B hB => ?_
      have hoffB : IsFFStarOffender G B := ((h4 B).2 ⟨i, hB⟩).1.1
      exact le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : IsFFStarOffender G B ∧ B ≤ G₂) => B)
        B ⟨hoffB, hB.1.trans (sl2_eq_iSup_sylow (h1a i).2 ▸ hiG₂ : _)⟩ le_rfl

end FFC

end CFSG.Quasithin
