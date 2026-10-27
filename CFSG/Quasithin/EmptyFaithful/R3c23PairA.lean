module

public import CFSG.Quasithin.EmptyFaithful.R3c23PairAFac
public import CFSG.Quasithin.EmptyFaithful.S153MTwoA
import CFSG.Quasithin.H13.NQRigidWMGroups

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace R3c23

section Cases

variable {V : Type} [CommGroup V] [Finite V]

private structure TwoCompData (J L₁ L₂ : Subgroup (MulAut V)) : Prop where
  comm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a
  q₁ : CFSG.IsQuasisimple ↥L₁
  q₂ : CFSG.IsQuasisimple ↥L₂
  le₁ : L₁ ≤ J
  le₂ : L₂ ≤ J
  norm : ∀ x ∈ J, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂
  two : ∀ x ∈ J, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂
  inf : L₁ ⊓ L₂ = ⊥
  card₁ : 60 ≤ Nat.card ↥L₁
  card₂ : 60 ≤ Nat.card ↥L₂
  ne₁ : Nat.card ↥L₁ ≠ 168
  ne₂ : Nat.card ↥L₂ ≠ 168

variable {J L₁ L₂ : Subgroup (MulAut V)}

omit [Finite V] in
private theorem TwoCompData.false_of_case1 (P : TwoCompData J L₁ L₂)
    (hF : CFSG.IsQuasisimple ↥(quasithinGenFitting J)) : False := by
  set F := quasithinGenFitting J with hFdef
  have hFJ : F ≤ J := quasithinGenFitting_le J
  have hLJ : L₁ ⊔ L₂ ≤ J := sup_le P.le₁ P.le₂
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (P.comm b hb a ha).symm
  have hL₁n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₁, x * k * x⁻¹ ∈ L₁ :=
    InternalSec.conj_mem_of_mem_sup_of_commute P.comm
  have hL₂n : ∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ L₂, x * k * x⁻¹ ∈ L₂ := by
    rw [sup_comm]
    exact InternalSec.conj_mem_of_mem_sup_of_commute hc'
  have hLJn : ((L₁ ⊔ L₂).subgroupOf J).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g g.2 n hn⟩
  have hcomp : ∀ {A : Subgroup (MulAut V)}, A ≤ L₁ ⊔ L₂ →
      (∀ x ∈ L₁ ⊔ L₂, ∀ k ∈ A, x * k * x⁻¹ ∈ A) → CFSG.IsQuasisimple ↥A → A ≤ F := by
    intro A hAL hAn hAq
    have hA : (A.subgroupOf (L₁ ⊔ L₂)).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        exact hAn g g.2 n hn⟩
    have hsub : CFSG.Open.IsSubnormal A J :=
      CFSG.Open.IsSubnormal.step hAL hA
        (CFSG.Open.IsSubnormal.step hLJ hLJn (CFSG.Open.IsSubnormal.refl J))
    have hc : CFSG.Open.IsComponentOf A J :=
      ⟨hAL.trans hLJ, hsub, B1Red.isQuasisimple_to_open hAq⟩
    exact (le_sSup (show A ∈ {K | CFSG.Open.IsComponentOf K J} from hc)).trans le_sup_right
  have hL₁F : L₁ ≤ F := hcomp le_sup_left hL₁n P.q₁
  have hL₂F : L₂ ≤ F := hcomp le_sup_right hL₂n P.q₂
  have hLF : L₁ ⊔ L₂ ≤ F := sup_le hL₁F hL₂F
  have hLFn : ((L₁ ⊔ L₂).subgroupOf F).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact P.norm g (hFJ g.2) n hn⟩
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hF) ((L₁ ⊔ L₂).subgroupOf F) with hcen | htop
  · refine InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb => ?_
    have h1 : (⟨a, hL₁F ha⟩ : ↥F) ∈ Subgroup.center ↥F :=
      hcen (show (⟨a, hL₁F ha⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F from Subgroup.mem_sup_left ha)
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hL₁F hb⟩
    exact (congrArg Subtype.val h2).symm
  · have hFL : F ≤ L₁ ⊔ L₂ := fun x hx => by
      have : (⟨x, hx⟩ : ↥F) ∈ (L₁ ⊔ L₂).subgroupOf F := htop ▸ Subgroup.mem_top _
      exact this
    have h1 : L₁ = F := twoG_eq_of_normal_of_isQuasisimple hL₁F
      (fun x hx k hk => hL₁n x (hFL hx) k hk) P.q₁ hF
    have h2 : L₂ = F := twoG_eq_of_normal_of_isQuasisimple hL₂F
      (fun x hx k hk => hL₂n x (hFL hx) k hk) P.q₂ hF
    have h12 : L₁ = L₂ := h1.trans h2.symm
    exact InternalSec.not_commute_of_isQuasisimple P.q₁ fun a ha b hb =>
      P.comm a ha b (h12 ▸ hb)

private theorem TwoCompData.false_of_case4 (P : TwoCompData J L₁ L₂) (h4 : B56Case4 J) : False := by
  obtain ⟨G₁, G₂, t, hJt, -, hcomm, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -, -⟩ := h4
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htN := InternalSec.mem_normalizer_sup ht₁ ht₂
  have hsol : Group.IsSolvable ↥G₂ := by
    have := isCyclic_of_prime_card hc₂
    infer_instance
  have hle : ∀ L : Subgroup (MulAut V), L ≤ J → CFSG.IsQuasisimple ↥L → L ≤ G₁ := by
    intro L hLJ hLq
    have h1 : L ≤ ⁅J, J⁆ := InternalSec.le_commutator_of_perfect hLJ hLq.1
    rw [hJt] at h1
    exact twoG_le_of_perfect_of_isSolvable hcomm
      (h1.trans (InternalSec.commutator_le_of_zpowers htN)) hLq.1 hsol
  have hsup : L₁ ⊔ L₂ ≤ G₁ := sup_le (hle L₁ P.le₁ P.q₁) (hle L₂ P.le₂ P.q₂)
  have h1 := Subgroup.card_le_of_le hsup
  have h2 := twoG_card_mul_le_card_sup P.inf
  have hcard : Nat.card ↥G₁ = 360 := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin]
    rfl
  have h3 := Nat.mul_le_mul P.card₁ P.card₂
  omega

private theorem TwoCompData.false_of_case5 (P : TwoCompData J L₁ L₂) (h5 : B56Case5 J) : False := by
  obtain ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, -⟩ := h5
  have hs : IsSimpleGroup ↥(StatedSL 3 (ZMod 2)) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_three_odd (m := 1) (by simp) odd_one
  have hs' : IsSimpleGroup ↥G₁ := e₁.isSimpleGroup
  have hcard : Nat.card ↥G₁ = 168 := by
    rw [Nat.card_congr e₁.toEquiv, twoG_card_statedSL_three, Nat.card_zmod]
    norm_num
  have hq : CFSG.IsQuasisimple ↥G₁ := twoG_isQuasisimple_of_simple (by rw [hcard]; norm_num)
  have hG₁J : G₁ ≤ J := by rw [← hsup]; exact le_sup_left
  have hn₁ : ∀ x ∈ J, ∀ g ∈ G₁, x * g * x⁻¹ ∈ G₁ := fun x hx g hg =>
    InternalSec.conj_mem_of_mem_sup_of_commute hc x (by rw [hsup]; exact hx) g hg
  rcases twoG_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two hG₁J hn₁ hq with h | h
  · exact P.ne₁ (by rw [← h]; exact hcard)
  · exact P.ne₂ (by rw [← h]; exact hcard)

private theorem TwoCompData.case3 (P : TwoCompData J L₁ L₂) (h3 : B56Case3 J) :
    ∃ (G₁ G₂ : Subgroup (MulAut V)) (W₁ W₂ : Subgroup V),
      J = G₁ ⊔ G₂ ∧ G₁ ⊓ G₂ = ⊥ ∧ (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) ∧ L₁ ≤ G₁ ∧ L₂ ≤ G₂ ∧
      (G₁ = L₁ ∨ (Nonempty (↥G₁ ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₁ = 60)) ∧
      (G₂ = L₂ ∨ (Nonempty (↥G₂ ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₂ = 60)) ∧
      fixV (G₁ ⊔ G₂) ≤ W₁ ∧ fixV (G₁ ⊔ G₂) ≤ W₂ ∧ W₁ ⊔ W₂ = ⊤ ∧
      W₁ ⊓ W₂ = fixV (G₁ ⊔ G₂) ∧ B56Piece G₁ W₁ (fixV (G₁ ⊔ G₂)) ∧
      B56Piece G₂ W₂ (fixV (G₁ ⊔ G₂)) := by
  obtain ⟨G₁, G₂, hsup, hinf, hc, hf₁, hf₂, W₁, W₂, hW₁, hW₂, -, -, hWsup, hWinf, hp₁, hp₂⟩ := h3
  have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hne : ∀ L : Subgroup (MulAut V), CFSG.IsQuasisimple ↥L → L ≠ ⊥ := by
    intro L hL hbot
    have : Nontrivial ↥L :=
      CFSG.ComponentClassification.Quasisimple.nontrivial (B1Red.isQuasisimple_to_open hL)
    have : Subsingleton ↥L := by rw [hbot]; infer_instance
    exact not_subsingleton ↥L ‹_›
  have key : ∀ {A B : Subgroup (MulAut V)}, A ⊔ B = J → A ⊓ B = ⊥ →
      (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → B56FactorList ↥A →
      (L₁ ≤ A ∧ (A = L₁ ∨ (Nonempty (↥A ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₁ = 60))) ∨
        (L₂ ≤ A ∧ (A = L₂ ∨ (Nonempty (↥A ≃* Equiv.Perm (Fin 5)) ∧ Nat.card ↥L₂ = 60))) := by
    intro A B hsupAB hinfAB hcAB hfA
    have hcBA : ∀ b ∈ B, ∀ a ∈ A, b * a = a * b := fun b hb a ha => (hcAB a ha b hb).symm
    have hAJ : A ≤ J := by rw [← hsupAB]; exact le_sup_left
    rcases twoG_fac_of_factorList hfA with ⟨K, hKA, hKn, hKq, hK⟩ | ⟨hsol, h3dvd⟩
    · have hKJn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K := by
        intro x hx k hk
        have hx' : x ∈ A ⊔ B := by rw [hsupAB]; exact hx
        obtain ⟨a, ha, b, hb, rfl⟩ :=
          (B19Aux.mem_sup_iff_of_le_normalizer
            (InternalSec.le_normalizer_of_commute hcAB)).1 hx'
        have hbk : b * k = k * b := (hcAB k (hKA hk) b hb).symm
        have e : a * b * k * (a * b)⁻¹ = a * k * a⁻¹ := by
          calc a * b * k * (a * b)⁻¹ = a * (b * k) * b⁻¹ * a⁻¹ := by group
            _ = a * (k * b) * b⁻¹ * a⁻¹ := by rw [hbk]
            _ = a * k * a⁻¹ := by group
        rw [e]
        exact hKn a ha k hk
      have hKL := twoG_eq_or_eq_of_normal P.comm P.q₁ P.q₂ P.le₁ P.le₂ P.two (hKA.trans hAJ) hKJn
        hKq
      rcases hKL with h | h
      · refine Or.inl ⟨by rw [← h]; exact hKA, ?_⟩
        rcases hK with h' | ⟨hS, h60⟩
        · exact Or.inl (h'.symm.trans h)
        · exact Or.inr ⟨hS, by rw [← h]; exact h60⟩
      · refine Or.inr ⟨by rw [← h]; exact hKA, ?_⟩
        rcases hK with h' | ⟨hS, h60⟩
        · exact Or.inl (h'.symm.trans h)
        · exact Or.inr ⟨hS, by rw [← h]; exact h60⟩
    · exfalso
      have hJBA : J = B ⊔ A := by rw [← hsupAB, sup_comm]
      have hL₁B : L₁ ≤ B :=
        twoG_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₁) P.q₁.1 hsol
      have hL₂B : L₂ ≤ B :=
        twoG_le_of_perfect_of_isSolvable hcBA (hJBA ▸ P.le₂) P.q₂.1 hsol
      have hLB : L₁ ⊔ L₂ ≤ B := sup_le hL₁B hL₂B
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3dvd
      obtain ⟨e, he⟩ := P.two (x : MulAut V) (hAJ x.2)
      have hxe : (x : MulAut V) ^ 2 ^ e ∈ A ⊓ B := ⟨A.pow_mem x.2 _, hLB he⟩
      rw [hinfAB, Subgroup.mem_bot] at hxe
      have hord : orderOf (x : MulAut V) = 3 := by rw [Subgroup.orderOf_coe, hx]
      have hdvd : 3 ∣ 2 ^ e := hord ▸ orderOf_dvd_of_pow_eq_one hxe
      have h32 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
      omega
  have hG₁ := key hsup hinf hc hf₁
  have hG₂ := key ((sup_comm _ _).trans hsup) ((inf_comm _ _).trans hinf) hc' hf₂
  rcases hG₁ with ⟨h1, k₁⟩ | ⟨h1, k₁⟩ <;> rcases hG₂ with ⟨h2, k₂⟩ | ⟨h2, k₂⟩
  · exfalso
    have : L₁ ≤ G₁ ⊓ G₂ := le_inf h1 h2
    rw [hinf, le_bot_iff] at this
    exact hne L₁ P.q₁ this
  · refine ⟨G₁, G₂, W₁, W₂, hsup.symm, hinf, hc, h1, h2, k₁, k₂, ?_⟩
    rw [hsup]
    exact ⟨hW₁, hW₂, hWsup, hWinf, hp₁, hp₂⟩
  · refine ⟨G₂, G₁, W₂, W₁, hsup.symm.trans (sup_comm _ _), (inf_comm _ _).trans hinf, hc', h2, h1,
      k₂, k₁, ?_⟩
    rw [sup_comm G₂ G₁, hsup]
    exact ⟨hW₂, hW₁, (sup_comm _ _).trans hWsup, (inf_comm _ _).trans hWinf, hp₂, hp₁⟩
  · exfalso
    have : L₂ ≤ G₁ ⊓ G₂ := le_inf h1 h2
    rw [hinf, le_bot_iff] at this
    exact hne L₂ P.q₂ this

end Cases

theorem twoB56Gen_of_ffModule (h56 : AsB56) {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {X L₁ L₂ : Subgroup (MulAut V)} {τ : MulAut V} (hτX : τ ∈ X)
    (hL₁X : L₁ ≤ X) (hL₂X : L₂ ≤ X) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hn : ∀ x ∈ X, ∀ l ∈ L₁ ⊔ L₂, x * l * x⁻¹ ∈ L₁ ⊔ L₂)
    (hτ : L₂ = L₁.map (MulAut.conj τ).toMonoidHom)
    (h2 : ∀ x ∈ X, ∃ e : ℕ, x ^ 2 ^ e ∈ L₁ ⊔ L₂)
    (hq₁ : CFSG.IsQuasisimple ↥L₁) (hq₂ : CFSG.IsQuasisimple ↥L₂) (hK : Lin2Cover ↥L₁)
    (hO2 : pCoreOf 2 X = ⊥) (hFF : IsFFModule X) (hB53 : B53Hyp (ffJ X)) :
    TwoB56Gen X L₁ L₂ := by
  obtain ⟨hL₁J, hL₂J⟩ := S153M.twoA_le_ffJ hV hτX hL₁X hL₂X hcomm hn hτ h2 hq₁ hq₂ hO2 hFF
  have hJX : ffJ X ≤ X := B6.ffJ_le X
  obtain ⟨hs₁, h60₁, hne₁⟩ := twoG_lin2Cover_facts hK
  have hcard₂ : Nat.card ↥L₂ = Nat.card ↥L₁ := by
    rw [hτ, Subgroup.card_map_of_injective (MulAut.conj τ).injective]
  have P : TwoCompData (ffJ X) L₁ L₂ :=
    ⟨hcomm, hq₁, hq₂, hL₁J, hL₂J, fun x hx l hl => hn x (hJX hx) l hl,
      fun x hx => h2 x (hJX hx), twoG_inf_eq_bot_of_commute hs₁ hq₁ hcomm, h60₁,
      by rw [hcard₂]; exact h60₁, hne₁, by rw [hcard₂]; exact hne₁⟩
  have hcases := h56 V hV (ffJ X) (InternalSec.ffJ_ne_bot_of_isFFModule hV hFF) hB53
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | h3 | h4 | h5
  · exact (P.false_of_case1 h1.1).elim
  · exact (InternalSec.not_le_perm_three hq₁ hL₁J e).elim
  · exact P.case3 h3
  · exact (P.false_of_case4 h4).elim
  · exact (P.false_of_case5 h5).elim

end R3c23

end CFSG.Quasithin
