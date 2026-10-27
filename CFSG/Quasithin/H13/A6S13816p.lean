module

public import CFSG.Quasithin.H13.A6S13816n
public import CFSG.Quasithin.H13.A6S13816o
public import CFSG.Quasithin.H13.NQRigidWMGroups
import CFSG.Quasithin.EmptyFaithful.S1565M7
public import CFSG.Quasithin.EmptyFaithful.S153MTwoData
public import CFSG.Quasithin.EmptyFaithful.S146xB2Excl

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open hiding StatedSL StatedSp
open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

namespace FFTwo

section Orders

theorem two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w)
    (h : 2 ^ a * u = 2 ^ b * w) : a = b := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu0 : u ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hu)
  have hw0 : w ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hw)
  have hu2 : ¬ 2 ∣ u := by have := Nat.odd_iff.mp hu; omega
  have hw2 : ¬ 2 ∣ w := by have := Nat.odd_iff.mp hw; omega
  have h1 := congrArg (padicValNat 2) h
  rw [padicValNat.mul (by positivity) hu0, padicValNat.mul (by positivity) hw0,
    padicValNat.prime_pow, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hu2,
    padicValNat.eq_zero_of_not_dvd hw2] at h1
  simpa using h1

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨c, hc⟩ : ∃ c, 2 ^ k = 2 * c := ⟨2 ^ (k - 1), by rw [← pow_succ']; congr 1; omega⟩
  exact ⟨c - 1, by omega⟩

theorem le_card_sl3 {m : ℕ} (hm : 1 ≤ m) :
    168 ≤ (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h8 : 8 ≤ (2 ^ m) ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left hq 3
  have h4 : 4 ≤ (2 ^ m) ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hq 2
  have := Nat.mul_le_mul h8 (Nat.mul_le_mul (show 3 ≤ (2 ^ m) ^ 2 - 1 by omega)
    (show 7 ≤ (2 ^ m) ^ 3 - 1 by omega))
  omega

theorem card_sl3_ne_card_sl2 {m n : ℕ} (hm : 1 ≤ m) :
    (2 ^ m) ^ 3 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) ≠ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  intro h
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hn1 : 1 ≤ n := by
    by_contra h0
    have hn0 : n = 0 := by omega
    subst hn0
    have := le_card_sl3 hm
    rw [h] at this
    norm_num at this
  have hodd1 : Odd (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) := by
    rw [← pow_mul, ← pow_mul]
    exact (odd_two_pow_sub_one (by omega)).mul (odd_two_pow_sub_one (by omega))
  have hodd2 : Odd ((2 ^ n) ^ 2 - 1) := by
    rw [← pow_mul]
    exact odd_two_pow_sub_one (by omega)
  have h' : 2 ^ (m * 3) * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by rw [pow_mul]; exact h
  have hn := two_pow_mul_odd_inj hodd1 hodd2 h'
  subst hn
  rw [Nat.mul_right_inj (by positivity), pow_mul] at h'
  set q := 2 ^ m with hqdef
  have hq3 : 1 ≤ q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have e : (q ^ 3) ^ 2 - 1 = (q ^ 3 - 1) * (q ^ 3 + 1) := by
    zify [hq3, Nat.one_le_pow 2 (q ^ 3) (by omega)]
    ring
  rw [e, mul_comm (q ^ 2 - 1)] at h'
  have hpos : 0 < q ^ 3 - 1 := by
    have : 8 ≤ q ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
    omega
  have h2 := Nat.eq_of_mul_eq_mul_left hpos h'
  have : q ^ 2 ≤ q ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

theorem card_sl2_ne {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 120 ∧ 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ 168 := by
  rcases Nat.lt_or_ge n 3 with h | h
  · have : n = 2 := by omega
    subst this
    norm_num
  · have hq : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 64 ≤ (2 ^ n) ^ 2 := by
        calc 64 = 8 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq 2
      omega
    have := Nat.mul_le_mul hq h63
    omega

end Orders

section Pieces

variable {V : Type} [CommGroup V] [Finite V]

omit [CommGroup V] [Finite V] in
theorem card_statedSL_two' {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 2 F) = Nat.card F * (Nat.card F ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_statedSL_two F

omit [CommGroup V] [Finite V] in
theorem card_statedSL_three' {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) =
      Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

omit [Finite V] in
theorem card_eq_of_natural {G : Subgroup (MulAut V)} {W C : Subgroup V} {d : ℕ} {K : Type}
    [Field K] [Finite K] (hR : (FFModel.nat (StatedSL d K)).Realizes G W C) :
    Nat.card ↥G = Nat.card ↥(StatedSL d K) := by
  obtain ⟨π, hπ⟩ : ∃ π : ↥(StatedSL d K) →* ↥G,
      (FFModel.nat (StatedSL d K)).RealizesVia G W C π := hR
  exact (Nat.card_congr (Equiv.ofBijective π ⟨natural_realizes_injective _ hπ, hπ.1⟩)).symm

omit [Finite V] in
theorem card_sl3_not_mem {K : Type} [Field K] [Finite K] {m n : ℕ} (hK : Nat.card K = 2 ^ m)
    {c : ℕ} (hc : c = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∨ c = 120) :
    Nat.card ↥(StatedSL 3 K) ≠ c := by
  have hm : 1 ≤ m := by
    by_contra h0
    have : m = 0 := by omega
    subst this
    have := Finite.one_lt_card (α := K)
    rw [hK] at this
    norm_num at this
  rw [card_statedSL_three', hK]
  rcases hc with rfl | rfl
  · exact card_sl3_ne_card_sl2 hm
  · have := le_card_sl3 hm
    omega

theorem piece_natural_or_sym {G L : Subgroup (MulAut V)} {W C : Subgroup V}
    (hp : B56Piece G W C) (hf : B56FactorList ↥G) (hLG : L ≤ G)
    (hLn : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) {n : ℕ}
    (hn : 2 ≤ n) (hcard : Nat.card ↥L = 2 ^ n * ((2 ^ n) ^ 2 - 1)) :
    (∃ m, BinaryNaturalSL G W C 2 m) ∨ SymmetricNatural G W C 5 := by
  have hL60 : 60 ≤ Nat.card ↥L := by
    rw [hcard]
    have hq4 : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have : 15 ≤ (2 ^ n) ^ 2 - 1 := by
      have : 16 ≤ (2 ^ n) ^ 2 := by
        calc 16 = 4 ^ 2 := by norm_num
          _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq4 2
      omega
    have := Nat.mul_le_mul hq4 this
    omega
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hL60
    omega
  have heq : IsSimpleGroup ↥G → L = G := by
    intro hs
    have hnorm : (L.subgroupOf G).Normal :=
      ⟨fun l hl g => by
        rw [Subgroup.mem_subgroupOf] at hl ⊢
        exact hLn g g.2 l hl⟩
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (L.subgroupOf G) with h | h
    · exfalso
      apply hLne
      rw [eq_bot_iff]
      intro l hl
      have : (⟨l, hLG hl⟩ : ↥G) ∈ L.subgroupOf G := hl
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    · refine le_antisymm hLG fun g hg => ?_
      have : (⟨g, hg⟩ : ↥G) ∈ L.subgroupOf G := h ▸ Subgroup.mem_top _
      exact this
  have hG : Nat.card ↥G = 2 ^ n * ((2 ^ n) ^ 2 - 1) ∨ Nat.card ↥G = 120 := by
    rcases hf with ⟨n', F, _, _, hn', hF, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨m, F, _, _, hm, hmodd, hF, ⟨e⟩⟩
    · have hcardG : Nat.card ↥G = Nat.card F * (Nat.card F ^ 2 - 1) := by
        rw [Nat.card_congr e.toEquiv, card_statedSL_two']
      by_cases hn1 : n' = 1
      · exfalso
        subst hn1
        have h6 : Nat.card ↥G = 6 := by rw [hcardG, hF]; norm_num
        have := Subgroup.card_le_of_le hLG
        omega
      · left
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        have := Fintype.ofFinite F
        have : CharP F 2 := charP_of_card_eq_prime_pow (f := n')
          (by rw [← Nat.card_eq_fintype_card, hF])
        have h4 : 4 ≤ Nat.card F := by
          rw [hF]
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) (by omega)
        have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
        have hs : IsSimpleGroup ↥G := e.isSimpleGroup
        rw [← heq hs, hcard]
    · right
      rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
      rfl
    · exfalso
      have := CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd hF hmodd
      have hs : IsSimpleGroup ↥G := e.isSimpleGroup
      have h1 := heq hs
      apply card_sl3_not_mem hF (Or.inl rfl)
      rw [← Nat.card_congr e.toEquiv, ← h1, hcard]
  rcases hp with ⟨-, h1 | h2 | ⟨m, K, _, _, hK, hR⟩⟩ | ⟨-, m, K, _, _, hK, I, π, -, -, -, hreal⟩ |
      ⟨⟨e⟩, -, -, -, -⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso
    rcases hG with h | h
    · exact card_sl3_not_mem hK (Or.inl rfl) ((card_eq_of_natural hR).symm.trans h)
    · exact card_sl3_not_mem (n := n) hK (Or.inr rfl) ((card_eq_of_natural hR).symm.trans h)
  · exfalso
    have hR : (FFModel.nat (StatedSL 3 K)).Realizes G (I 0) C := ⟨π, hreal 0⟩
    rcases hG with h | h
    · exact card_sl3_not_mem hK (Or.inl rfl) ((card_eq_of_natural hR).symm.trans h)
    · exact card_sl3_not_mem (n := n) hK (Or.inr rfl) ((card_eq_of_natural hR).symm.trans h)
  · exfalso
    have h168 : Nat.card ↥G = 168 := by
      rw [Nat.card_congr e.toEquiv, card_statedSL_three', Nat.card_zmod]
      norm_num
    rcases hG with h | h
    · exact (card_sl2_ne hn).2 (h.symm.trans h168)
    · omega

end Pieces

section Strong

variable {V : Type} [CommGroup V] [Finite V]

theorem TwoB56Gen.card_mul_card_fixV_le {X L₁ L₂ : Subgroup (MulAut V)} (h : TwoB56Gen X L₁ L₂)
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hc₁ : Nat.card ↥L₁ = 2 ^ n₁ * ((2 ^ n₁) ^ 2 - 1))
    (hc₂ : Nat.card ↥L₂ = 2 ^ n₂ * ((2 ^ n₂) ^ 2 - 1)) {A : Subgroup (MulAut V)} (hAX : A ≤ X)
    (hA1 : A ≠ ⊥) (hA2 : IsElemAbelian2 A) : Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card V := by
  obtain ⟨G₁, G₂, W₁, W₂, hL₁, hL₂, hN₁, hN₂, hsup, hinf, hc, hf₁, hf₂, -, -, hI₁, hI₂, hWsup,
    hWinf, hp₁, hp₂⟩ := h
  have hG₁J : G₁ ≤ ffJ X := hsup ▸ le_sup_left
  have hG₂J : G₂ ≤ ffJ X := hsup ▸ le_sup_right
  have hbound : ∀ {G L : Subgroup (MulAut V)} {W : Subgroup V} {n : ℕ},
      B56Piece G W (fixV (ffJ X)) → B56FactorList ↥G → L ≤ G →
      (∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L) → 2 ≤ n → Nat.card ↥L = 2 ^ n * ((2 ^ n) ^ 2 - 1) →
      ∀ B : Subgroup (MulAut V), B ≤ G → IsElemAbelian2 B →
        Nat.card ↥B * Nat.card ↥(fixMod B W (fixV (ffJ X))) ≤ Nat.card ↥W := by
    intro G L W n hp hf hLG hLn hn hcard B hBG hB
    rcases piece_natural_or_sym hp hf hLG hLn hn hcard with ⟨m, hm⟩ | hs
    · exact card_mul_card_fixMod_le_natural hm hBG hB.2
    · exact card_mul_card_fixMod_le_sym hs hBG hB
  have hinv : ∀ {G : Subgroup (MulAut V)} {W : Subgroup V}, G ≤ ffJ X →
      XMod.IsInv ↥(ffJ X) W → ∀ g ∈ G, ∀ w ∈ W, g w ∈ W :=
    fun hGJ hI g hg w hw => hI ⟨g, hGJ hg⟩ w hw
  have hmove : ∀ {G : Subgroup (MulAut V)} {W W' : Subgroup V}, G ≤ ffJ X →
      B56Piece G W' (fixV (ffJ X)) → XMod.IsInv ↥(ffJ X) W → W' ⊓ W = fixV (ffJ X) →
      ∀ g ∈ G, ∀ w ∈ W, g w * w⁻¹ ∈ fixV (ffJ X) := by
    intro G W W' hGJ hp hI hWW g hg w hw
    rw [← hWW]
    exact ⟨commV_le_of_b56Piece hp (Subgroup.subset_closure ⟨g, hg, w, rfl⟩),
      W.mul_mem (hI ⟨g, hGJ hg⟩ w hw) (W.inv_mem hw)⟩
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨B, ⟨hBA, hB0⟩, hmax⟩ := Set.exists_max_image
    {B : Subgroup (MulAut V) | B ≤ A ∧ B ≠ ⊥} (fun B => Nat.card ↥B * Nat.card ↥(fixV B))
    (Set.toFinite _) ⟨A, le_rfl, hA1⟩
  have hAmax : Nat.card ↥A * Nat.card ↥(fixV A) ≤ Nat.card ↥B * Nat.card ↥(fixV B) :=
    hmax A ⟨le_rfl, hA1⟩
  have hBe : IsElemAbelian2 B := B6.isElemAbelian2_mono hA2 hBA
  have hBoff : IsFFStarOffender X B := by
    refine ⟨hBA.trans hAX, hB0, hBe, fun B' hB' => ?_⟩
    by_cases hB'0 : B' = ⊥
    · subst hB'0
      rw [B1.card_bot_mul_card_fixV]
      exact hlt.le.trans hAmax
    · exact hmax B' ⟨hB'.trans hBA, hB'0⟩
  have hBJ : B ≤ G₁ ⊔ G₂ := hsup ▸ B6.le_ffJ hBoff
  have := card_mul_card_fixV_le_of_factors hc hinf hWsup hWinf
    (fun g hg c hc => hc g (hG₁J hg)) (fun g hg c hc => hc g (hG₂J hg))
    (hinv hG₁J hI₁) (hinv hG₂J hI₂) (hmove hG₁J hp₁ hI₂ hWinf)
    (hmove hG₂J hp₂ hI₁ (by rw [inf_comm]; exact hWinf))
    (hbound hp₁ hf₁ hL₁ hN₁ hn₁ hc₁) (hbound hp₂ hf₂ hL₂ hN₂ hn₂ hc₂) hBJ hBe
  omega

theorem TwoB56Gen.not_isStrongFFModule {X L₁ L₂ : Subgroup (MulAut V)} (h : TwoB56Gen X L₁ L₂)
    {n₁ n₂ : ℕ} (hn₁ : 2 ≤ n₁) (hn₂ : 2 ≤ n₂) (hc₁ : Nat.card ↥L₁ = 2 ^ n₁ * ((2 ^ n₁) ^ 2 - 1))
    (hc₂ : Nat.card ↥L₂ = 2 ^ n₂ * ((2 ^ n₂) ^ 2 - 1)) : ¬ IsStrongFFModule X := by
  rintro ⟨A, hAX, hA1, hA2, hlt⟩
  have := h.card_mul_card_fixV_le hn₁ hn₂ hc₁ hc₂ hAX hA1 hA2
  omega

end Strong

section Action

variable {V : Type} [CommGroup V] [Finite V]

theorem twoSum_of_action (hA21 : AsA21SQTKSection) (h56 : AsB56) {Hg : Type} [Group Hg]
    [Finite Hg] (hS : SQTKGroup Hg) (hV : ∀ v : V, v ^ 2 = 1) (ρ : Hg →* MulAut V)
    (K₁ : Subgroup Hg) (t : Hg) (hqK : CFSG.IsQuasisimple (↥K₁ ⧸ CFSG.pCore 2 ↥K₁))
    (hKn : (K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom).Normal)
    (hcomm : ⁅K₁, K₁.map (MulAut.conj t).toMonoidHom⁆ ≤ CFSG.pCore 2 Hg)
    (hQ : CFSG.pCore 2 Hg ≤ ρ.ker)
    (h2 : ∀ y : Hg, ∃ e : ℕ, y ^ 2 ^ e ∈ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom)
    (hperm : ∀ x : Hg, x ∈ Subgroup.normalizer (K₁ : Set Hg) ∨
      t⁻¹ * x ∈ Subgroup.normalizer (K₁ : Set Hg))
    (hnt : ¬ K₁ ⊔ K₁.map (MulAut.conj t).toMonoidHom ≤ ρ.ker) (hFF : IsFFModule ρ.range)
    {n : ℕ} (hK : IsPSL 2 2 n ↥(K₁.map ρ)) :
    commV (K₁.map ρ) ≤ fixV ((K₁.map (MulAut.conj t).toMonoidHom).map ρ) ∧
      ¬ IsStrongFFModule ρ.range := by
  obtain ⟨hq₁, hq₂, hc, hconj, hn', h2', hO2⟩ :=
    S153M.ar_facts_two ρ K₁ t hqK hKn hcomm hQ h2 hperm hnt
  have hτX : ρ t ∈ ρ.range := ⟨t, rfl⟩
  have hL₁X : K₁.map ρ ≤ ρ.range := Subgroup.map_le_range ρ K₁
  have hL₂X : (K₁.map (MulAut.conj t).toMonoidHom).map ρ ≤ ρ.range := Subgroup.map_le_range ρ _
  obtain ⟨hL₁J, hL₂J⟩ := S153M.twoA_le_ffJ hV hτX hL₁X hL₂X hc hn' hconj h2' hq₁ hq₂ hO2 hFF
  have hB53 := S153M.b53Hyp_of_two hA21 hS ρ hq₁ hq₂ hc hL₁J hL₂J hn' h2' hO2
  have hn1 : 1 ≤ n := hK.1.2.1
  have hn2 : 2 ≤ n := by
    by_contra h0
    have hn : n = 1 := by omega
    subst hn
    exact hK.1.2.2.2.1 rfl
  have hcard₁ : Nat.card ↥(K₁.map ρ) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [card_of_isPSL_two_even hn1 hK, ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  have hcard₂ : Nat.card ↥((K₁.map (MulAut.conj t).toMonoidHom).map ρ) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [hconj, Subgroup.card_map_of_injective (MulAut.conj (ρ t)).injective, hcard₁]
  have hinf : K₁.map ρ ⊓ (K₁.map (MulAut.conj t).toMonoidHom).map ρ = ⊥ := by
    have hs : IsSimpleGroup ↥(K₁.map ρ) := isSimpleGroup_of_psl2_or_sz (Or.inl hK)
    have hcen : Subgroup.center ↥(K₁.map ρ) = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥(K₁.map ρ)) with h | h
      · exact h
      · exfalso
        apply InternalSec.not_commute_of_isQuasisimple hq₁
        intro a ha b hb
        have hb' : (⟨b, hb⟩ : ↥(K₁.map ρ)) ∈ Subgroup.center ↥(K₁.map ρ) := h ▸ Subgroup.mem_top _
        exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hb' ⟨a, ha⟩))
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxc : (⟨x, hx.1⟩ : ↥(K₁.map ρ)) ∈ Subgroup.center ↥(K₁.map ρ) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2 x hx.2)
    rw [hcen, Subgroup.mem_bot] at hxc
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxc)
  have hne := card_sl2_ne hn2
  have hbig : 360 < Nat.card ↥(K₁.map ρ) *
      Nat.card ↥((K₁.map (MulAut.conj t).toMonoidHom).map ρ) := by
    rw [hcard₁, hcard₂]
    have h60 : 60 ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
      have hq4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have : 15 ≤ (2 ^ n) ^ 2 - 1 := by
        have : 16 ≤ (2 ^ n) ^ 2 := by
          calc 16 = 4 ^ 2 := by norm_num
            _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left hq4 2
        omega
      have := Nat.mul_le_mul hq4 this
      omega
    nlinarith
  have hT := twoB56Gen_of_ffModule h56 hV hτX hL₁X hL₂X hc hn' hconj h2' hq₁ hq₂ hinf
    (by rw [hcard₁]; exact hne.2) (by rw [hcard₂]; exact hne.2) hbig hO2 hFF hB53
  exact ⟨hT.commV_le_fixV hq₂.1, hT.not_isStrongFFModule hn2 hn2 hcard₁ hcard₂⟩

end Action

end FFTwo

end CFSG.Quasithin.H13.A6
