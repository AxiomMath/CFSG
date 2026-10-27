module

public import CFSG.Quasithin.H13.L32AC41a
public import CFSG.Quasithin.H13.L32AC32g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

theorem sl2_inv_eq : ∀ s r : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), s ^ 2 = 1 →
    (s * r) ^ 2 = 1 → r ≠ 1 → r ^ 2 = 1 → s = 1 ∨ s = r := by
  decide

theorem sl2_gen' : ∀ p : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ×
    Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) × Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    p.1 ≠ 1 → p.1 ^ 3 = 1 → p.2.1 ≠ 1 → p.2.1 ^ 2 = 1 →
      p.2.2 = 1 ∨ p.2.2 = p.1 ∨ p.2.2 = p.1 * p.1 ∨ p.2.2 = p.2.1 ∨ p.2.2 = p.2.1 * p.1 ∨
        p.2.2 = p.2.1 * (p.1 * p.1) := by
  decide +kernel

theorem sl2_gen (a g h : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hg1 : g ≠ 1) (hg2 : g ^ 2 = 1) :
    h = 1 ∨ h = a ∨ h = a * a ∨ h = g ∨ h = g * a ∨ h = g * (a * a) :=
  sl2_gen' (a, g, h) ha1 ha3 hg1 hg2

theorem sl2_trich : ∀ a h : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), a ≠ 1 → a ^ 3 = 1 →
    h = 1 ∨ h = a ∨ h = a * a ∨ h ^ 2 = 1 := by
  decide

theorem sl2_relIndex_eq_three {A R : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2))}
    {a r : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)} (ha : a ∈ A) (ha1 : a ≠ 1)
    (ha3 : a ^ 3 = 1) (hr : r ∈ R) (hr1 : r ≠ 1) (hR : ∀ s ∈ R, s ^ 2 = 1) :
    R.relIndex A = 3 := by
  have hRr : ∀ s ∈ R, s = 1 ∨ s = r := fun s hs =>
    sl2_inv_eq s r (hR s hs) (hR _ (R.mul_mem hs hr)) hr1 (hR r hr)
  have hr2 := hR r hr
  have hmul := Subgroup.relIndex_mul_card R A
  by_cases hrA : r ∈ A
  · have hA : A = ⊤ := by
      refine eq_top_iff.mpr fun h _ => ?_
      rcases sl2_gen a r h ha1 ha3 hr1 hr2 with rfl | rfl | rfl | rfl | rfl | rfl
      · exact A.one_mem
      · exact ha
      · exact A.mul_mem ha ha
      · exact hrA
      · exact A.mul_mem hrA ha
      · exact A.mul_mem hrA (A.mul_mem ha ha)
    have hcardR : Nat.card R = 2 := by
      rw [Nat.card_eq_two_iff]
      refine ⟨1, ⟨r, hr⟩, fun h => hr1 (congrArg Subtype.val h).symm, ?_⟩
      ext ⟨s, hs⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      rcases hRr s hs with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    rw [hA, inf_top_eq, hcardR, Subgroup.card_top, L32NSet14.card_sl2] at hmul
    rw [hA]
    omega
  · have hinf : R ⊓ A = ⊥ := by
      refine (Subgroup.eq_bot_iff_forall _).mpr fun s hs => ?_
      rcases hRr s hs.1 with h | h
      · exact h
      · exact absurd (h ▸ hs.2) hrA
    have hAz : A = Subgroup.zpowers a := by
      refine le_antisymm (fun h hh => ?_) (Subgroup.zpowers_le.mpr ha)
      rcases sl2_trich a h ha1 ha3 with e | e | e | h2
      · rw [e]
        exact one_mem _
      · rw [e]
        exact Subgroup.mem_zpowers _
      · rw [e]
        exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)
      · by_cases hh1 : h = 1
        · rw [hh1]
          exact one_mem _
        · exfalso
          apply hrA
          rcases sl2_gen a h r ha1 ha3 hh1 h2 with e | e | e | e | e | e <;> rw [e]
          · exact A.one_mem
          · exact ha
          · exact A.mul_mem ha ha
          · exact hh
          · exact A.mul_mem hh ha
          · exact A.mul_mem hh (A.mul_mem ha ha)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    rw [hinf, Subgroup.card_bot, mul_one] at hmul
    rw [hmul, hAz, Nat.card_zpowers, orderOf_eq_prime ha3 ha1]

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem isSolvable_szB1_of (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H) :
    Group.IsSolvable ↥(szB1 T H K) := by
  have hS := isSylowIn_szS1_of S hK
  have hSB : szS1 T H K ≤ szB1 T H K := le_inf Subgroup.le_normalizer hS.le
  refine isSolvable_of_isPGroup_odd hSB inf_le_left hS.isPGroup ?_
  have hmul := Subgroup.relIndex_mul_relIndex _ _ _ hSB (inf_le_right : szB1 T H K ≤ _)
  have hodd : Odd ((szS1 T H K).relIndex (modO2Image H K)) :=
    Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hS.not_dvd_relIndex)
  exact (Nat.odd_mul.mp (hmul ▸ hodd)).1

theorem isSolvable_szB1_l1T (hN1 : LieSylowOver3) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (cStar K)) (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ}
    (hn : 1 < n) (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K)))
    (hl1K : l1 T L V ≤ K) :
    Group.IsSolvable ↥(szB1 T H K ⊔ modO2Image H (l1 T L V ⊔ T)) := by
  have hN := l1T_le_normalizer_szS1 hN1 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hBN : modO2Image H (l1 T L V ⊔ T) ≤
      Subgroup.normalizer (szB1 T H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro z hz
    have hzS := hN hz
    obtain ⟨w, -, rfl⟩ := mem_modO2Image'.mp hz
    exact mem_normalizer_szB1 hzS (mk_mem_normalizer hKH (hKn w.2))
  exact isSolvable_sup_of_le_normalizer' hBN (isSolvable_szB1_of S hK)
    (isSolvable_l1T_star h1222 h1332 h1334 S)

theorem mem_normalizer_L_of_solvable (h29 : Thm14_7_29) (S : Setting147 G T L V H)
    {X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hX : Group.IsSolvable ↥X)
    (hLT : modO2Image H (l1 T L V ⊔ T) ≤ X) {β : ↥H}
    (hβ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) β ∈ X) :
    (β : G) ∈ Subgroup.normalizer (L : Set G) := by
  have hLTH : l1 T L V ⊔ T ≤ H := sup_le (Setting147.l1H' S) (Setting147.TH' S)
  have hLTY : l1 T L V ⊔ T ≤ (X.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype :=
    fun z hz => Subgroup.mem_map.mpr ⟨⟨z, hLTH hz⟩, hLT (mem_modO2Image'.mpr ⟨_, hz, rfl⟩), rfl⟩
  exact h29 G T L V S.hyp _ hLTY ((Subgroup.map_subtype_le _).trans S.hz.2.1)
    (isSolvable_preimage hX) (Subgroup.mem_map.mpr ⟨β, hβ, rfl⟩)

theorem mem_nX_of (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H)
    {β : G} (hβH : β ∈ H) (hβL : β ∈ Subgroup.normalizer (L : Set G)) :
    β ∈ L32NSet14.nX T V := by
  have hVc : conjClosure (fsuV1 T V) L = V :=
    (h1334 G T L V S.hyp.hyp.h13 (S.hyp.hyp1223 (stmt13_3_2_two_of h1332)).irrPlus).2.1
  have hβ1 : β ∈ Subgroup.normalizer (fsuV1 T V : Set G) := S.hz.2.1 hβH
  refine ⟨?_, hβ1⟩
  rw [← hVc]
  exact SzN16.mem_normalizer_conjClosure hβL hβ1

section Comm

variable {V₂ : Subgroup G} [IsMulCommutative ↥V]

theorem pCoreOf_L_nX_le_T (h : Hyp147 G T L V) (S14 : L32NSet14.Setting G T L V V₂) :
    pCoreOf 2 (L ⊓ L32NSet14.nX T V) ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : T ≤ Subgroup.normalizer ((L ⊓ L32NSet14.nX T V : Subgroup G) : Set G) :=
    fun r hr => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨S14.TL hr, Subgroup.le_normalizer (S14.T_le_X hr)⟩
  have hN : (L ⊓ L32NSet14.nX T V) ⊔ T ≤
      Subgroup.normalizer (pCoreOf 2 (L ⊓ L32NSet14.nX T V) : Set G) :=
    sup_le (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 _))
      (hTN.trans (normalizer_le_normalizer_pCoreOf 2 _))
  exact (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) hN
    (pCoreOf_isPGroup 2 _)).trans (L32A.pCoreOf_le_of_le h le_sup_right)

theorem comm_mem_T (h : Hyp147 G T L V) (S14 : L32NSet14.Setting G T L V V₂)
    {ψ : ↥(L32NSet14.nX T V) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)}
    (hψ : ∀ x, ψ x = 1 ↔ (x : G) ∈ L32NSet14.trivSub V (fsuV1 T V))
    {t : G} (htT : t ∈ T) (htL : t ∈ L) {β : G} (hβX : β ∈ L32NSet14.nX T V)
    (hβL : β ∈ Subgroup.normalizer (L : Set G)) {τ : G} (hτT : τ ∈ T)
    (hτ : ψ ⟨τ, S14.T_le_X hτT⟩ = ψ ⟨β, hβX⟩) :
    t * β * t⁻¹ * β⁻¹ ∈ T := by
  have hτX := S14.T_le_X hτT
  have htX := S14.T_le_X htT
  have hwX : τ⁻¹ * β ∈ L32NSet14.nX T V := mul_mem (inv_mem hτX) hβX
  have hwt : τ⁻¹ * β ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    have e : (⟨τ⁻¹ * β, hwX⟩ : ↥(L32NSet14.nX T V)) = ⟨τ, hτX⟩⁻¹ * ⟨β, hβX⟩ := rfl
    refine (hψ ⟨τ⁻¹ * β, hwX⟩).mp ?_
    rw [e, map_mul, map_inv, hτ, inv_mul_cancel]
  have hwL : τ⁻¹ * β ∈ Subgroup.normalizer (L : Set G) := mul_mem (inv_mem (S14.TL hτT)) hβL
  set w := τ⁻¹ * β with hw
  have hcL : t * w * t⁻¹ * w⁻¹ ∈ L := by
    have h1 : w * t⁻¹ * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hwL _).mp (inv_mem htL)
    have e : t * w * t⁻¹ * w⁻¹ = t * (w * t⁻¹ * w⁻¹) := by group
    rw [e]
    exact mul_mem htL h1
  have hcX : t * w * t⁻¹ * w⁻¹ ∈ L32NSet14.nX T V :=
    mul_mem (mul_mem (mul_mem htX hwX) (inv_mem htX)) (inv_mem hwX)
  have hct : t * w * t⁻¹ * w⁻¹ ∈ L32NSet14.trivSub V (fsuV1 T V) :=
    mul_mem (L32NSet14.conj_mem_trivSub htX.1 htX.2 hwt) (inv_mem hwt)
  have hcT : t * w * t⁻¹ * w⁻¹ ∈ T :=
    pCoreOf_L_nX_le_T h S14 (S14.le_pCoreOf inf_le_right (inf_le_left.trans le_sup_left)
      ⟨⟨hcL, hcX⟩, hct⟩)
  have e : t * β * t⁻¹ * β⁻¹ = (t * τ * t⁻¹ * τ⁻¹) * (τ * (t * w * t⁻¹ * w⁻¹) * τ⁻¹) := by
    rw [hw]
    group
  rw [e]
  exact mul_mem (mul_mem (mul_mem (mul_mem htT hτT) (inv_mem htT)) (inv_mem hτT))
    (mul_mem (mul_mem hτT hcT) (inv_mem hτT))

end Comm

end CFSG.Quasithin.H13.L32A.C
