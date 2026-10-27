module

public import CFSG.Quasithin.Vol2.Ch12Sec1Stmts
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.Quasithin.Vol2.Ch11SecA02Simple
public import CFSG.Quasithin.Background.E3Nlow
public import CFSG.Quasithin.Vol2.Ch12Sec2Statements

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

namespace Sec121Thm

variable {G : Type} [Group G]

theorem isElemAbelian_of_isPrimeReduced {V M : Subgroup G} (hVM : V ≤ M)
    (hred : IsPrimeReduced 2 (V.subgroupOf M)) : IsElemAbelian 2 V := by
  have := hred.isElementaryAbelian
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
  · have h := mul_comm (⟨⟨a, hVM a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩ : ↥(V.subgroupOf M))
      ⟨⟨b, hVM b.2⟩, Subgroup.mem_subgroupOf.mpr b.2⟩
    exact congrArg (fun z : ↥(V.subgroupOf M) => ((z : ↥M) : G)) h
  · have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf M)
      (⟨x, hVM hx⟩ : ↥M) (Subgroup.mem_subgroupOf.mpr hx)
    simpa using congrArg Subtype.val h2

theorem isQuasisimple_of_mulEquiv {E S : Type*} [Group E] [Group S] [IsSimpleGroup S]
    (hS : ∃ a b : S, a * b ≠ b * a) (e : E ≃* S) : CFSG.IsQuasisimple E := by
  have : IsSimpleGroup E := e.isSimpleGroup
  have hE : ∃ a b : E, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hS
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    simpa using congrArg e h
  have hZ : Subgroup.center E = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center E) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hE
      exact hab ((Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b)) a)
  have eZ : E ⧸ Subgroup.center E ≃* E :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  refine ⟨⟨?_⟩, eZ.isSimpleGroup, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator E) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hE
      have : ⁅a, b⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← h]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      exact hab (commutatorElement_eq_one_iff_mul_comm.mp this)
    · exact h
  · obtain ⟨a, b, hab⟩ := hE
    refine ⟨eZ.symm a, eZ.symm b, fun h => hab ?_⟩
    simpa using congrArg eZ h

theorem exists_mul_of_mem_sup {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {c : G} (hc : c ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = c := by
  rw [Subgroup.sup_eq_closure] at hc
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, mul_one x⟩
    · exact ⟨1, A.one_mem, x, hx, one_mul x⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ihx
    obtain ⟨a', ha', b', hb', rfl⟩ := ihy
    refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
    rw [show a * b * (a' * b') = a * (b * a') * b' by group, ← hAB a' ha' b hb]
    group
  | inv x _ ih =>
    obtain ⟨a, ha, b, hb, rfl⟩ := ih
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    rw [mul_inv_rev, hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)]

theorem exists_not_commute_SL {n : ℕ} (hn : 3 ≤ n) :
    ∃ a b : Matrix.SpecialLinearGroup (Fin n) (ZMod 2), a * b ≠ b * a := by
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two hn
  by_contra h
  have hZ : Subgroup.center (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) = ⊤ :=
    eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun y => not_not.mp fun hxy =>
      h ⟨y, x, hxy⟩
  have h1 := CFSG.Quasithin.Vol2.Ch11.SecA.card_center_SL_zmod_two (n := n) (by omega)
  rw [hZ, Subgroup.card_top] at h1
  have := (Nat.card_eq_one_iff_unique.mp h1).1
  obtain ⟨g, hg⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin n) (ZMod 2))
  exact hg (Subsingleton.elim _ _)

variable [Finite G]

theorem isQuasisimple_of_hyp121 {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp121 G T L V V₁ V₂ n) : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e⟩ := hyp.iso
  have hn3 : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  have : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) :=
    CFSG.Quasithin.Vol2.Ch11.SecA.isSimpleGroup_SL_zmod_two hn3
  exact isQuasisimple_of_mulEquiv (exists_not_commute_SL hn3) e

theorem ne_bot_of_hyp121 {T L V V₁ V₂ : Subgroup G} {n : ℕ}
    (hyp : Hyp121 G T L V V₁ V₂ n) : V ≠ ⊥ := by
  intro hbot
  obtain ⟨e⟩ := hyp.iso
  obtain ⟨φ⟩ := hyp.aut
  have hn3 : 3 ≤ n := by rcases hyp.rank with h | h <;> omega
  have : Subsingleton ↥V := by rw [hbot]; infer_instance
  have hsub : Subsingleton (MulAut ↥V) :=
    ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
  obtain ⟨a, b, hab⟩ := exists_not_commute_SL hn3
  have hc : MulAut.conj (e.symm a) ≠ 1 := by
    intro h1
    apply hab
    have h2 := congrArg (fun f : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) => e (f (e.symm b))) h1
    simp only [MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply,
      MulAut.one_apply] at h2
    calc a * b = a * b * a⁻¹ * a := by group
      _ = b * a := by rw [h2]
  apply hc
  have h3 : φ.symm (MulAut.conj (e.symm a)) = φ.symm 1 := Subtype.ext (Subsingleton.elim _ _)
  exact φ.symm.injective h3

theorem normalizer_eq_of_hyp121 (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1)
    {T L V V₁ V₂ : Subgroup G} {n : ℕ} (hyp : Hyp121 G T L V V₁ V₂ n) :
    T ≤ Subgroup.normalizer (L : Set G) ∧
      Subgroup.normalizer (V : Set G) = Subgroup.normalizer (L : Set G) := by
  have hqs := isQuasisimple_of_hyp121 hyp
  have hTL := h1001 G T L hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hyp.maximal hyp.faithful hqs
  refine ⟨hTL, ?_⟩
  have hLT : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl)
      (le_conjClosure L T)
  obtain ⟨⟨hMmax, -, -⟩, -⟩ :=
    (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal hqs
  rw [hLT] at hMmax
  obtain ⟨hnorm, -, -⟩ := hyp.reduced
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hyp.le).mp hnorm
  have hVe := isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  exact hMmax.2 _ ⟨V, ne_bot_of_hyp121 hyp, hV2, rfl⟩ hMV

end Sec121Thm

open Sec121Thm

theorem lem1212_one_of (h1211 : Lem1211) {G : Type} [Group G] [Finite G]
    {T L V V₁ V₂ : Subgroup G} {n : ℕ} {β : G → G → ZMod 2} (hyp : Hyp121 G T L V V₁ V₂ n)
    (hβ : IsDualPairing121 L V₁ V₂ β) (U : Subgroup G) (hUV : U ≤ V)
    (hC : ¬ Subgroup.centralizer (U : Set G) ≤ Subgroup.normalizer (L : Set G)) (u : G)
    (hu : u ∈ U) : IsSingular121 V₁ V₂ β u := by
  have hmem : u ∈ V₁ ⊔ V₂ := hyp.sup ▸ hUV hu
  have hcomm : ∀ a ∈ V₁, ∀ c ∈ V₂, a * c = c * a := by
    have hV := isElemAbelian_of_isPrimeReduced hyp.le hyp.reduced
    intro a ha c hc
    have h1 : a ∈ V := hyp.sup ▸ Subgroup.mem_sup_left ha
    have h2 : c ∈ V := hyp.sup ▸ Subgroup.mem_sup_right hc
    have := hV.1
    exact congrArg Subtype.val (mul_comm (⟨a, h1⟩ : ↥V) ⟨c, h2⟩)
  obtain ⟨a, ha, c, hc, rfl⟩ := exists_mul_of_mem_sup hcomm hmem
  have h01 : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases h01 (β a c) with h0 | h1
  · exact ⟨a, ha, c, hc, rfl, h0⟩
  · exfalso
    apply hC
    exact (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hu)).trans
      (h1211 G T L V V₁ V₂ n β hyp hβ _ (hUV hu) ⟨a, ha, c, hc, rfl, h1⟩)

theorem stmt12_1_11_of (h1001 : Stmt10_0_1) (h331 : Stmt3_3_1) (hQ : Setup121Q)
    (h1217 : Lem1217) (h1218 : Lem1218) (h1219 : Lem1219) (h12110 : Lem12110) : Stmt12_1_11 := by
  intro G _ _ T L hs hna hq hT hmax hf n hn hiso V V₁ V₂ hVL hred haut hinf hsup hL1 hL2 hnat1
    hnat2 hdual
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp : Hyp121 G T L V V₁ V₂ n :=
    ⟨hs, hna, hq, hT, hmax, hf, hn, hiso, hVL, hred, haut, hinf, hsup, hL1, hL2, hnat1, hnat2,
      hdual⟩
  obtain ⟨hTL, hNV⟩ := normalizer_eq_of_hyp121 h1001 h331 hyp
  have hQ := hQ G T L V V₁ V₂ n hyp hTL
  have hqs := isQuasisimple_of_hyp121 hyp
  have hLT : conjClosure L T = L :=
    le_antisymm (conjClosure_le fun t ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl)
      (le_conjClosure L T)
  obtain ⟨⟨hMmax, hLTM, huniqLT⟩, -, ⟨H, hH⟩, -, -⟩ := (h331 G T hs hna hq hT).2 L hmax hqs
  rw [hLT] at hMmax hLTM huniqLT hH
  have hVe := isElemAbelian_of_isPrimeReduced hVL hred
  have hV2 : IsPGroup 2 ↥V := fun x => ⟨1, Subtype.ext (by simpa using hVe.2 x x.2)⟩
  have hV1 : V ≠ ⊥ := ne_bot_of_hyp121 hyp
  have hMV : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (V : Set G) := hNV.ge
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hTL.trans hMV
  have hVT : V ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVL hMV hV2).trans
      (B6.pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hT hTL))
  have h322 : HypE322 T V :=
    ⟨⟨le_top, hT.1, by rw [Subgroup.relIndex_top_right]; exact hT.2⟩, hVT, hTV⟩
  have hQne : T ⊓ Subgroup.centralizer (V : Set G) ≠ ⊥ := by
    intro hbot
    apply hV1
    rw [eq_bot_iff, ← hbot]
    intro v hv
    refine ⟨hVT hv, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    have := hVe.1
    exact congrArg Subtype.val (mul_comm (⟨w, hw⟩ : ↥V) ⟨v, hv⟩)
  have hNQ : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    hQ ▸ CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
  have huniqQ : IsUniqueM (Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
      (Subgroup.normalizer (L : Set G)) := by
    have hloc : IsTwoLocal (Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) :=
      ⟨_, hQne, hT.1.to_le inf_le_left, rfl⟩
    obtain ⟨M'', hM'', hle⟩ := exists_maxTwoLocal_ge hloc
    have hM''eq : M'' = Subgroup.normalizer (L : Set G) := huniqLT M'' hM'' (hNQ.trans hle)
    exact ⟨⟨hMmax, hM''eq ▸ hle⟩, fun M' hM' => huniqLT M' hM'.1 (hNQ.trans hM'.2)⟩
  have hS : IsSylowIn 2 T H :=
    ⟨hH.1.1, hT.1, fun h => hT.2 (h.trans (Subgroup.relIndex_dvd_index_of_le hH.1.1))⟩
  have hCH : H ⊓ Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    fun x hx => by rw [← hNV]; exact Subgroup.centralizer_le_normalizer _ hx.2
  have hw : (3 : ℕ∞) ≤ wParam T V := by
    refine le_iInf₂ fun j hj => ?_
    have hj3 : 3 ≤ j := by
      by_contra hlt
      apply hj
      interval_cases j
      · exact h1217 G T L V V₁ V₂ n hyp
      · exact h1218 G T L V V₁ V₂ n hyp
      · exact h12110 G T L V V₁ V₂ n hyp
    exact_mod_cast hj3
  obtain ⟨-, hnH, hr⟩ := h1219 G T L V V₁ V₂ n hyp
  have hlt : E1.nParam H < min (wParam T V) (rParam V) := by
    rw [hnH H hH]
    refine lt_min (lt_of_lt_of_le (by decide) hw) (lt_of_lt_of_le ?_ hr)
    exact_mod_cast (by omega : 2 < n + 2)
  exact hH.2.1 (e3_35_one hVe hV1 h322 huniqQ hS hCH inf_le_left hlt)

end CFSG.Quasithin.H13
