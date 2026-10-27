module

public import CFSG.Quasithin.EmptyFaithful.T1521SA5Tr
public import CFSG.Quasithin.EmptyFaithful.T1521SA5Orb
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.EmptyFaithful.T1521SDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCS2Model
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InBlk2
public import CFSG.Quasithin.Background.C2Coprime
public import CFSG.Quasithin.Background.B1MoreSevenA
public import CFSG.Quasithin.Background.B2FactorizationR2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.A5S5
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_odd_order_acts_trivially {K A : Subgroup G} (hK : IsShort2 K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hKA : ⁅K, A⁆ ≤ pCoreOf 2 K)
    (hU : A ≤ Subgroup.centralizer (blockU K : Set G))
    (hodd : ∀ a ∈ A, ∃ m : ℕ, Odd m ∧ a ^ m = 1) : A ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨hK1, -, ⟨-, hsq⟩, -⟩ := hK
  have hKC : K ≤ Subgroup.centralizer (A : Set G) := by
    refine C2Coprime.le_of_forall_odd_order hK1 fun x hx n hn hxn => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hq : a * x * a⁻¹ * x⁻¹ ∈ blockU K :=
      C2Coprime.commutator_mem_blockU hAK hKA hx ha hn hxn
    obtain ⟨m, hm, ham⟩ := hodd a ha
    have hfix : a * (a * x * a⁻¹ * x⁻¹) * a⁻¹ = a * x * a⁻¹ * x⁻¹ := by
      have := Subgroup.mem_centralizer_iff.mp (hU ha) _ hq
      calc a * (a * x * a⁻¹ * x⁻¹) * a⁻¹ = (a * (a * x * a⁻¹ * x⁻¹)) * a⁻¹ := rfl
        _ = ((a * x * a⁻¹ * x⁻¹) * a) * a⁻¹ := by rw [← this]
        _ = a * x * a⁻¹ * x⁻¹ := by group
    obtain ⟨q, hqdef⟩ : ∃ q, q = a * x * a⁻¹ * x⁻¹ := ⟨_, rfl⟩
    rw [← hqdef] at hq hfix
    have hpow : ∀ k : ℕ, a ^ k * x * (a ^ k)⁻¹ = q ^ k * x := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        have h1 : a * q ^ k * a⁻¹ = q ^ k := by rw [← conj_pow, hfix]
        have h2 : a * x * a⁻¹ = q * x := by rw [hqdef]; group
        calc a ^ (k + 1) * x * (a ^ (k + 1))⁻¹ = a * (a ^ k * x * (a ^ k)⁻¹) * a⁻¹ := by group
          _ = a * (q ^ k * x) * a⁻¹ := by rw [ih]
          _ = (a * q ^ k * a⁻¹) * (a * x * a⁻¹) := by group
          _ = q ^ (k + 1) * x := by rw [h1, h2, pow_succ, mul_assoc]
    have h1 : q ^ m = 1 := by
      have := hpow m
      rw [ham] at this
      simpa using this.symm
    have hq2 : q ^ 2 = 1 := by simpa [pow_two] using hsq q hq
    have hq1 : q = 1 := by
      obtain ⟨j, rfl⟩ := hm
      rw [pow_succ, pow_mul, hq2, one_pow, one_mul] at h1
      exact h1
    have : a * x * a⁻¹ = x := by
      have := hq1
      rw [hqdef] at this
      calc a * x * a⁻¹ = (a * x * a⁻¹ * x⁻¹) * x := by group
        _ = x := by rw [this, one_mul]
    calc a * x = a * x * a⁻¹ * a := by group
      _ = x * a := by rw [this]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact (Subgroup.mem_centralizer_iff.mp (hKC hk) a ha).symm

theorem centralizes_of_normalizes_blockA5 {X S L Y : Subgroup G} {p : ℕ} (hStd : Std1521 X S L)
    (hth : ⁅L, thompsonJ S⁆ = L) (hblk : IsBlock2 X L) (h5 : IsAltType L 5) (hp : p = 3 ∨ p = 5)
    (hYJ : Y ≤ Subgroup.normalizer (thompsonJ S : Set G))
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hY : IsPGroup p Y) : ⁅L, Y⁆ = ⊥ := by
  have hshort : IsShort2 L := hblk.1
  have hJN : thompsonJ S ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_commutator_eq hth
  obtain ⟨α, hα, hαk, -⟩ := id h5
  obtain ⟨P, -⟩ := exists_a5pi hshort h5 α hα hαk
  have hmemQ : ∀ x : ↥L, P.α x = 1 ↔ (x : G) ∈ pCoreOf 2 L := fun x => by
    rw [← MonoidHom.mem_ker, P.hαk, Lin2.mem_pCoreOf_iff_mem_pCore]
  have hQS : pCoreOf 2 L ≤ S ⊓ L := pCoreOf_le_of_isSylowTwoOf hStd.sylowL
  have hKL : S ⊓ L ≤ L := inf_le_right
  have hker : P.α.ker ≤ (S ⊓ L).subgroupOf L := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hQS ((hmemQ x).1 hx))
  have hKalt : imageUnder P.π (S ⊓ L) ≤ alternatingGroup (Fin 5) :=
    imageUnder_le_alt Subgroup.le_normalizer P.α P.hπα hKL
  have hKcard : Nat.card (imageUnder P.π (S ⊓ L)) = 4 :=
    card_imageUnder_eq_four Subgroup.le_normalizer P.α P.hπα P.hα hKL hker hStd.sylowL.2.1
      hStd.sylowL.2.2
  have hA : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    rfl
  have hLQ : ¬ L ≤ blockQ L := by
    intro hLQ
    have hall : ∀ x : alternatingGroup (Fin 5), x = 1 := by
      intro x
      obtain ⟨l, rfl⟩ := P.hα x
      exact (hmemQ l).2 (hLQ l.2)
    have : Subsingleton (alternatingGroup (Fin 5)) := ⟨fun a b => (hall a).trans (hall b).symm⟩
    have h1 : Nat.card (alternatingGroup (Fin 5)) = 1 := Nat.card_of_subsingleton 1
    omega
  obtain ⟨y1, hy1J, hy1⟩ :=
    AppCS2.exists_mem_thompsonJ_pi_ne_one' P.toPiData hshort hth hJN hLQ
  have hU : IsElemAbelian 2 (blockU L) :=
    C5.isElemAbelian_two_iff.2 (C1.elemAb2_blockU hshort)
  have hUQ : blockU L ≤ pCoreOf 2 L := (le_inf_iff.1 hshort.2.2.1.1).1
  have hUS : blockU L ≤ S := hUQ.trans (hQS.trans inf_le_left)
  have hcl := AppCS2.swapGen_imJ' P.toPiData hU hUS hJN _ (P.toPiData.pi_mem_im hy1J)
  obtain ⟨s, hsJ, hsw⟩ : ∃ s ∈ P.im (thompsonJ S), s.IsSwap := by
    by_contra hcon
    push Not at hcon
    have hempty : {s : Equiv.Perm (Fin 5) | s ∈ P.im (thompsonJ S) ∧ s.IsSwap} = ∅ :=
      Set.eq_empty_of_forall_notMem fun s hs => hcon s hs.1 hs.2
    rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at hcl
    exact hy1 hcl
  obtain ⟨j, hjJ, hjs⟩ := (P.toPiData.mem_im).1 hsJ
  have hodd : ∃ j : ↥(Subgroup.normalizer (L : Set G)), (j : G) ∈ thompsonJ S ∧
      Equiv.Perm.sign (P.π j) = -1 := ⟨j, hjJ, by rw [hjs]; exact hsw.sign_eq⟩
  have hS₁pg : IsPGroup 2 (S ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) :=
    hStd.sylow.2.1.to_le inf_le_left
  have hKS₁ : S ⊓ L ≤ S ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf inf_le_left (inf_le_right.trans Subgroup.le_normalizer)
  have hJS₁ : thompsonJ S ≤ S ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf (thompsonJ_le_self S) hJN
  have hS₁J : (S ⊓ Subgroup.normalizer (L : Set G) : Subgroup G) ≤
      Subgroup.normalizer (thompsonJ S : Set G) := fun s hs =>
    normalizer_le_normalizer_thompsonJ S (Subgroup.le_normalizer hs.1)
  have key := eq_one_of_normalizes_odd (π := P.π) (S := S ⊓ Subgroup.normalizer (L : Set G))
    (J := thompsonJ S) (K := S ⊓ L) (Y := Y) hp hKS₁ hJS₁ hS₁pg hKalt hKcard hodd hS₁J hYJ hY
  have hKA : ⁅L, Y⁆ ≤ pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro l hl y hy
    have hyN : y ∈ Subgroup.normalizer (L : Set G) := hYL hy
    have hyL : y * l⁻¹ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hyN _).mp (L.inv_mem hl)
    have hcom : ⁅l, y⁆ = l * (y * l⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
    have hcL : ⁅l, y⁆ ∈ L := by rw [hcom]; exact L.mul_mem hl hyL
    have hπ : P.π (⟨l, Subgroup.le_normalizer hl⟩ * ⟨y, hyN⟩ * ⟨l, Subgroup.le_normalizer hl⟩⁻¹ *
        ⟨y, hyN⟩⁻¹) = 1 := by
      have hy1 := key ⟨y, hyN⟩ hy
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
      simp
    have hxx : (⟨l, Subgroup.le_normalizer hl⟩ * ⟨y, hyN⟩ * ⟨l, Subgroup.le_normalizer hl⟩⁻¹ *
        ⟨y, hyN⟩⁻¹ : ↥(Subgroup.normalizer (L : Set G))) =
        ⟨⁅l, y⁆, Subgroup.le_normalizer hcL⟩ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [hxx, P.hπα _ hcL] at hπ
    exact (hmemQ ⟨⁅l, y⁆, hcL⟩).1 (Subtype.ext hπ)
  have hUY : Y ≤ Subgroup.centralizer (blockU L : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := (P.hker ⟨y, hYL hy⟩).1 (key ⟨y, hYL hy⟩ hy) u hu
    calc u * y = (y * u * y⁻¹) * y := by rw [h1]
      _ = y * u := by group
  have hYC := le_centralizer_of_odd_order_acts_trivially hshort hYL hKA hUY
    (exists_odd_pow_eq_one_of_isPGroup hp hY)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro l hl y hy
  exact (Subgroup.mem_centralizer_iff.1 (hYC hy) l hl).symm

theorem exc1521_blockA5_of_orbits (horb : A3Orbits G) {X S L : Subgroup G} (hStd : Std1521 X S L)
    (hth : ⁅L, thompsonJ S⁆ = L) (hblk : IsBlock2 X L) (h5 : IsAltType L 5) :
    Exc1521 X S L := by
  obtain ⟨hXS, hcase⟩ := horb X S L hStd.sqtk hStd.sylow hStd.comp
  intro p Y hp hYX hYJ _ hY _
  have hYL : Y ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_orbits hXS (hcase.imp id fun h => by
      obtain ⟨t, htS, -, hset, -⟩ := h
      exact ⟨t, htS, hset⟩) hYX (exists_odd_pow_eq_one_of_isPGroup hp hY)
  exact centralizes_of_normalizes_blockA5 hStd hth hblk h5 hp hYJ hYL hY

theorem dich1521BlockA5_of_orbits (horb : ∀ (G : Type) [Group G] [Finite G], A3Orbits G) :
    Dich1521BlockA5 := by
  intro G _ _ X S L hStd hth _ hblk h5
  exact Or.inr (exc1521_blockA5_of_orbits (horb G) hStd hth hblk h5)

end CFSG.Quasithin
