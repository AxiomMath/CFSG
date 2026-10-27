module

public import CFSG.Quasithin.H13.U3S1347H
public import CFSG.Quasithin.EmptyFaithful.T1531Cat
public import CFSG.Quasithin.H13.KGFactL2
public import CFSG.Quasithin.H13.NQS134Defs
public import CFSG.Quasithin.H13.U3S1347G

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem card_map_pPrimeCore {I A : Subgroup G} (hAI : A ≤ I) :
    Nat.card ↥((A.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) =
      ((CFSG.pPrimeCore 3 ↥I).map I.subtype).relIndex A := by
  rw [F6.card_map_mk, ← relIndex_map_map_of_injective _ _ I.subtype_injective,
    map_subgroupOf_eq_of_le hAI]

omit [Finite G] in
theorem le_normalizer_map_subtype {I : Subgroup G} (M : Subgroup ↥I) [hM : M.Normal] :
    I ≤ normalizer ((M.map I.subtype : Subgroup G) : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨g, hg⟩ * y * ⟨g, hg⟩⁻¹, hM.conj_mem y hy _, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨g, hg⟩⁻¹ * y * ⟨g, hg⟩⁻¹⁻¹, hM.conj_mem y hy _, ?_⟩
    have e : x = g⁻¹ * (y : G) * g := by
      rw [show (y : G) = g * x * g⁻¹ from hyx]
      group
    rw [e]
    simp

omit [Finite G] in
theorem commutator_subgroupOf_eq {K I : Subgroup G} (hKI : K ≤ I) (hperf : ⁅K, K⁆ = K) :
    ⁅K.subgroupOf I, K.subgroupOf I⁆ = K.subgroupOf I := by
  apply map_injective I.subtype_injective
  rw [map_commutator, map_subgroupOf_eq_of_le hKI, hperf]

theorem s1347_K0 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2)
    (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5) (h1345 : NQS134.Stmt13_4_5) (hF : F6.TheoremF618Cat)
    (hBig : A5.FactF618Big) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (h : Hyp1347 T H₁ H₂) (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂)) :
    ∃ K₀ : Subgroup G, K₀ ∈ cComp (H₁ ⊔ H₂) ∧ H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G) ∧
      (quasithinIsMaximalLocal T K₀ ∧ quasithinIsFaithfulLocal T K₀) ∧
      (LieModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) .PSL 3 2 1 ∨
        Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6))) ∧
      oTwoRes H₁ ≤ K₀ ∧ oTwoRes H₂ ≤ K₀ ∧ H₁ ⊔ H₂ = K₀ ⊔ T ∧
      K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hH₀, hH₀M, -⟩ := s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hred := s1347_reduced S hH₀
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hsyl₀ := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hsyl₁ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₁.1
  have hsyl₂ := A5.isSylowTwoOf_of_le S.h13.sylow h.inH₂.1
  obtain ⟨⟨K₀, hK₀⟩, hall⟩ := h1345 G T L V S (H₁ ⊔ H₂) hH₀ hH₀M hns
  obtain ⟨hloc, hN, hcases, -, -, -, -, ⟨VK, hVK⟩, hVKall⟩ := hall K₀ hK₀
  obtain ⟨-, -, -, -, -, hcent⟩ := hVKall VK hVK
  have hKH := le_of_mem_cComp hK₀
  have hcases' : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) .PSL 3 2 1 ∨
      Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)) := by
    rcases hcases with h5 | h32 | h6 | hhat
    · exact Or.inl h5
    · exact Or.inr (Or.inl h32)
    · exact Or.inr (Or.inr h6)
    · exact absurd hhat (s1347_not_hat S h hH₀ hKH hcent)
  obtain ⟨hs, hcK⟩ := simple_of_cases hcases'
  have h3 : 3 ∣ Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by
    rcases hcK with e | e | e <;> rw [e] <;> norm_num
  have hrel : (pCoreOf 2 K₀).relIndex K₀ = Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by
    rw [relIndex, pCoreOf_subgroupOf_eq_pCore]
    rfl
  obtain ⟨N3, hN3⟩ : ∃ X : Subgroup G,
      X = (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)).map (H₁ ⊔ H₂).subtype := ⟨_, rfl⟩
  have hN3n : H₁ ⊔ H₂ ≤ normalizer (N3 : Set G) := hN3 ▸ le_normalizer_map_subtype _
  have hN3c : Nat.Coprime 3 (Nat.card N3) := by
    rw [hN3, card_map_of_injective (H₁ ⊔ H₂).subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hKN3 : K₀ ⊓ N3 ≤ pCoreOf 2 K₀ :=
    inf_le_pCoreOf_of_coprime_three (hKH.trans hN3n) hN3c hs h3
  have hO₀ : pCoreOf 2 K₀ ≤ pCoreOf 2 (H₁ ⊔ H₂) := pCoreOf_le_pCoreOf hKH hN
  have hON3 : pCoreOf 2 (H₁ ⊔ H₂) ≤ N3 := by
    rw [hN3]
    exact map_mono F6.pCore_le_pPrimeCore
  have hinf : K₀ ⊓ N3 = pCoreOf 2 K₀ :=
    le_antisymm hKN3 (le_inf (pCoreOf_le 2 K₀) (hO₀.trans hON3))
  have hsylK : IsSylowTwoOf (T ⊓ K₀) K₀ := A4.isSylowTwoOf_inf_normal hsyl₀ hKH hN
  have hOT : pCoreOf 2 K₀ ≤ T ⊓ K₀ := pCoreOf_two_le_of_isSylowTwoOf hsylK
  have hTK : T ⊓ K₀ ≤ H₁ ⊔ H₂ := inf_le_right.trans hKH
  have hinfT : (T ⊓ K₀) ⊓ N3 = pCoreOf 2 K₀ :=
    le_antisymm ((inf_le_inf_right N3 inf_le_right).trans hKN3) (le_inf hOT (hO₀.trans hON3))
  have hcardN : Nat.card ↥((K₀.subgroupOf (H₁ ⊔ H₂)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)))) =
      Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := by
    rw [card_map_pPrimeCore hKH, ← hN3, ← inf_relIndex_right, inf_comm, hinf, hrel]
  have hcardP : Nat.card ↥(((T ⊓ K₀).subgroupOf (H₁ ⊔ H₂)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)))) =
      (pCoreOf 2 K₀).relIndex (T ⊓ K₀) := by
    rw [card_map_pPrimeCore hTK, ← hN3, ← inf_relIndex_right, inf_comm, hinfT]
  have hm := relIndex_mul_relIndex (pCoreOf 2 K₀) (T ⊓ K₀) K₀ hOT inf_le_right
  rw [hrel] at hm
  have hrel0 : (pCoreOf 2 K₀).relIndex (T ⊓ K₀) ≠ 0 := index_ne_zero_of_finite
  have hodd : Nat.Coprime 2 ((T ⊓ K₀).relIndex K₀) :=
    Nat.coprime_two_left.2 (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hsylK.2.2))
  have hdvd : ∀ j : ℕ, 2 ^ j ∣ Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) →
      2 ^ j ≤ (pCoreOf 2 K₀).relIndex (T ⊓ K₀) := fun j hj => by
    refine Nat.le_of_dvd (Nat.pos_of_ne_zero hrel0) ((Nat.Coprime.pow_left j
      hodd).dvd_of_dvd_mul_right ?_)
    rw [hm]
    exact hj
  have h4 : 4 ≤ (pCoreOf 2 K₀).relIndex (T ⊓ K₀) :=
    hdvd 2 (by rcases hcK with e | e | e <;> rw [e] <;> norm_num)
  have h8 : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≠ 60 → 8 ≤ (pCoreOf 2 K₀).relIndex (T ⊓ K₀) :=
    fun h60 => hdvd 3 (by
      rcases hcK with e | e | e
      · exact absurd e h60
      · rw [e]; norm_num
      · rw [e]; norm_num)
  have hT := s1347_triple S h
  rcases hT.f6_18Cat hF (stronglyQuasithin_of_pCoreOf_ne_bot S.h13.qtke hH₀.2)
    (kGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian hH₀.2) with
    ⟨-, hAm, -, hconc⟩ | ⟨-, -, hS3, -, -⟩
  swap
  ·
    exfalso
    obtain ⟨e⟩ := hS3
    have h1 := card_le_of_le (le_top : (K₀.subgroupOf (H₁ ⊔ H₂)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) ≤ ⊤)
    rw [card_top, Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 3),
      Fintype.card_fin, hcardN] at h1
    rcases hcK with e' | e' | e' <;> rw [e'] at h1 <;> norm_num [Nat.factorial] at h1
  have hKn : (K₀.subgroupOf (H₁ ⊔ H₂)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hKH).2 hN
  have hP2 : IsPGroup 2 ↥((T ⊓ K₀).subgroupOf (H₁ ⊔ H₂)) :=
    hsylK.2.1.of_equiv (subgroupOfEquivOfLe hTK).symm
  obtain ⟨hNO, hN60⟩ := eq_oTwoUpper_of_f618 hBig A5.factL2Three_holds hAm hconc
    (hKn.map _ (QuotientGroup.mk'_surjective _))
    (by rw [← map_commutator, commutator_subgroupOf_eq hKH (perfect_of_mem_cComp hK₀)])
    (map_mono fun x hx => mem_subgroupOf.2 ((inf_le_right : T ⊓ K₀ ≤ K₀) (mem_subgroupOf.1 hx)))
    (hP2.map _) (by rw [hcardP]; exact h4)
    (by
      rcases eq_or_ne (Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) 60 with e | e
      · exact Or.inl ⟨0, by rw [hcardN, e]; rfl⟩
      · exact Or.inr (by rw [hcardP]; exact h8 e))
  have hnot5 : ¬ Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 5)) := by
    rintro ⟨e⟩
    apply hN60 0
    rw [hcardN, Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hKi : ∀ {Hi : Subgroup G}, Hi ≤ H₁ ⊔ H₂ → T ≤ Hi → T.relIndex Hi = 3 →
      oTwoRes Hi ≤ K₀ := by
    intro Hi hHi hTi h3i
    refine (closure_le _).2 fun x hx => ?_
    obtain ⟨hxH, m, hm, hxm⟩ := hx
    have hx3 : (⟨x, hHi hxH⟩ : ↥(H₁ ⊔ H₂)) ^ 3 ^ 1 = 1 := Subtype.ext (by
      simpa using pow_three_of_relIndex_three S.h13.sylow.1 hTi h3i hxH hm hxm)
    have hmem : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂)) ⟨x, hHi hxH⟩ ∈
        (K₀.subgroupOf (H₁ ⊔ H₂)).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(H₁ ⊔ H₂))) := by
      rw [hNO]
      refine mem_oTwoUpper_of_odd (mem_top _) (Odd.of_dvd_nat (by decide : Odd 3)
        (orderOf_dvd_of_pow_eq_one ?_))
      rw [← map_pow, show (⟨x, hHi hxH⟩ : ↥(H₁ ⊔ H₂)) ^ 3 = 1 by simpa using hx3, map_one]
    exact mem_subgroupOf.1 (A5.mem_of_pow_three_of_mem_map hT.isSolvable_pPrimeCore
      (subgroupOf_mem_cComp hK₀) hx3 hmem)
  have hK₁ := hKi le_sup_left h.inH₁.1 h3₁
  have hK₂ := hKi le_sup_right h.inH₂.1 h3₂
  have hsup : H₁ ⊔ H₂ = K₀ ⊔ T := by
    refine le_antisymm (sup_le ?_ ?_) (sup_le hKH hsyl₀.1)
    · exact (le_oTwoRes_sup_of_isSylowTwoOf hsyl₁).trans (sup_le_sup_right hK₁ T)
    · exact (le_oTwoRes_sup_of_isSylowTwoOf hsyl₂).trans (sup_le_sup_right hK₂ T)
  have hCn : H₁ ⊔ H₂ ≤ normalizer (((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) :
      Subgroup G) : Set G) := fun g hg =>
    mem_normalizer_inf_of (le_normalizer hg) (mem_normalizer_centralizer_of_mem (hred.2.1 hg))
  have hCc : Nat.Coprime 3 (Nat.card ↥((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G))) := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    intro h3d
    obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' 3 h3d
    have hx1 := s1347_eq_one_of_threePow S h hH₀ hx (k := 1) (by
      have h1 := pow_orderOf_eq_one (⟨x, hx⟩ : ↥((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G)))
      rw [hxo] at h1
      simpa using congrArg Subtype.val h1)
    subst hx1
    rw [show (⟨1, hx⟩ : ↥((H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G))) = 1 from rfl,
      orderOf_one] at hxo
    omega
  have hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀ := by
    refine le_antisymm ?_ (le_inf (pCoreOf_le 2 K₀)
      (hO₀.trans ((s1347_T_inf_centralizer S h hH₀).ge.trans inf_le_right)))
    refine le_trans ?_ (inf_le_pCoreOf_of_coprime_three (hKH.trans hCn) hCc hs h3)
    exact le_inf inf_le_left (le_inf (inf_le_left.trans hKH) inf_le_right)
  exact ⟨K₀, hK₀, hN, hloc, hcases'.resolve_left hnot5, hK₁, hK₂, hsup, hcentK⟩

end CFSG.Quasithin.H13.U3
