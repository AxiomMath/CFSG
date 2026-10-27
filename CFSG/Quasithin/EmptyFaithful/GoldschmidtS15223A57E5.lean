module

public import CFSG.Quasithin.EmptyFaithful.T1521SA5Blk
public import CFSG.Quasithin.Background.A1cRank

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.A5S5 CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem exists_sign_neg_of_alt5 {X Q₁ A : Subgroup G} (P : A5Pi X)
    (hU : IsElemAbelian 2 (blockU X)) (hUQ : blockU X ≤ Q₁)
    (hQN : Q₁ ≤ Subgroup.normalizer (X : Set G)) (hA : IsMaxElemAbelian Q₁ A)
    (hAc : ¬ A ≤ Subgroup.centralizer (blockU X : Set G)) :
    ∃ j : ↥(Subgroup.normalizer (X : Set G)), (j : G) ∈ A ∧ Equiv.Perm.sign (P.π j) = -1 := by
  have hAN : A ≤ Subgroup.normalizer (X : Set G) := hA.1.trans hQN
  have hcl := P.toPiData.swapGen_im hU hUQ hQN hA
  obtain ⟨a, haA, hac⟩ : ∃ a ∈ A, a ∉ Subgroup.centralizer (blockU X : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hAc hcon
  have hπa : P.π ⟨a, hAN haA⟩ ≠ 1 := by
    intro h1
    apply hac
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h2 := (P.hker ⟨a, hAN haA⟩).1 h1 u hu
    calc u * a = (a * u * a⁻¹) * a := by rw [h2]
      _ = a * u := by group
  obtain ⟨s, hsA, hsw⟩ : ∃ s ∈ P.im A, s.IsSwap := by
    by_contra hcon
    push Not at hcon
    have hempty : {s : Equiv.Perm (Fin 5) | s ∈ P.im A ∧ s.IsSwap} = ∅ :=
      Set.eq_empty_of_forall_notMem fun s hs => hcon s hs.1 hs.2
    have := hcl _ (P.toPiData.pi_mem_im (K := A) (y := ⟨a, hAN haA⟩) haA)
    rw [hempty, Subgroup.closure_empty, Subgroup.mem_bot] at this
    exact hπa this
  obtain ⟨j, hjA, hjs⟩ := (P.toPiData.mem_im).1 hsA
  exact ⟨j, hjA, by rw [hjs]; exact hsw.sign_eq⟩

theorem commutator_eq_bot_of_alt5_odd {X S J Y : Subgroup G} (hshort : IsShort2 X) (P : A5Pi X)
    (hS2 : IsPGroup 2 S) (hsyl : IsSylowTwoOf (S ⊓ X) X) (hJS : J ≤ S)
    (hSJ : S ≤ Subgroup.normalizer (J : Set G)) (hYJ : Y ≤ Subgroup.normalizer (J : Set G))
    (hYX : Y ≤ Subgroup.normalizer (X : Set G)) (hY : IsPGroup 3 Y)
    (hodd : ∃ j : ↥(Subgroup.normalizer (X : Set G)), (j : G) ∈ J ∧
      Equiv.Perm.sign (P.π j) = -1) : ⁅X, Y⁆ = ⊥ := by
  have hp : (3 : ℕ) = 3 ∨ (3 : ℕ) = 5 := Or.inl rfl
  have hmemQ : ∀ x : ↥X, P.α x = 1 ↔ (x : G) ∈ pCoreOf 2 X := fun x => by
    rw [← MonoidHom.mem_ker, P.hαk, Lin2.mem_pCoreOf_iff_mem_pCore]
  have hQS : pCoreOf 2 X ≤ S ⊓ X := pCoreOf_le_of_isSylowTwoOf hsyl
  have hKL : S ⊓ X ≤ X := inf_le_right
  have hker : P.α.ker ≤ (S ⊓ X).subgroupOf X := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hQS ((hmemQ x).1 hx))
  have hKalt : imageUnder P.π (S ⊓ X) ≤ alternatingGroup (Fin 5) :=
    imageUnder_le_alt Subgroup.le_normalizer P.α P.hπα hKL
  have hKcard : Nat.card (imageUnder P.π (S ⊓ X)) = 4 :=
    card_imageUnder_eq_four Subgroup.le_normalizer P.α P.hπα P.hα hKL hker hsyl.2.1 hsyl.2.2
  have key := eq_one_of_normalizes_odd (π := P.π) (S := S) (J := J) (K := S ⊓ X) (Y := Y) hp
    inf_le_left hJS hS2 hKalt hKcard hodd hSJ hYJ hY
  have hKA : ⁅X, Y⁆ ≤ pCoreOf 2 X := by
    rw [Subgroup.commutator_le]
    intro l hl y hy
    have hyN : y ∈ Subgroup.normalizer (X : Set G) := hYX hy
    have hyL : y * l⁻¹ * y⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hyN _).mp (X.inv_mem hl)
    have hcom : ⁅l, y⁆ = l * (y * l⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
    have hcL : ⁅l, y⁆ ∈ X := by rw [hcom]; exact X.mul_mem hl hyL
    have hπ : P.π (⟨l, Subgroup.le_normalizer hl⟩ * ⟨y, hyN⟩ * ⟨l, Subgroup.le_normalizer hl⟩⁻¹ *
        ⟨y, hyN⟩⁻¹) = 1 := by
      have hy1 := key ⟨y, hyN⟩ hy
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
      simp
    have hxx : (⟨l, Subgroup.le_normalizer hl⟩ * ⟨y, hyN⟩ * ⟨l, Subgroup.le_normalizer hl⟩⁻¹ *
        ⟨y, hyN⟩⁻¹ : ↥(Subgroup.normalizer (X : Set G))) =
        ⟨⁅l, y⁆, Subgroup.le_normalizer hcL⟩ :=
      Subtype.ext (by simp [commutatorElement_def])
    rw [hxx, P.hπα _ hcL] at hπ
    exact (hmemQ ⟨⁅l, y⁆, hcL⟩).1 (Subtype.ext hπ)
  have hUY : Y ≤ Subgroup.centralizer (blockU X : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 := (P.hker ⟨y, hYX hy⟩).1 (key ⟨y, hYX hy⟩ hy) u hu
    calc u * y = (y * u * y⁻¹) * y := by rw [h1]
      _ = y * u := by group
  have hYC := le_centralizer_of_odd_order_acts_trivially hshort hYX hKA hUY
    (exists_odd_pow_eq_one_of_isPGroup hp hY)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro l hl y hy
  exact (Subgroup.mem_centralizer_iff.1 (hYC hy) l hl).symm

theorem false_of_centralizes_block {I X P : Subgroup G}
    (hrank : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) ≤ 2) (hXI : X ≤ I) (hPI : P ≤ I)
    (hP : IsElemAbelian 3 P) (hP9 : Nat.card P = 9) (hX : IsShort2 X) (h3 : 3 ∣ Nat.card X)
    (hPc : P ≤ Subgroup.centralizer (X : Set G)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 h3
  have hx' : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hx
  have hxX : (x : G) ∈ X := x.2
  have hcomm : ∀ e ∈ P, Commute e (x : G) := fun e he =>
    (Subgroup.mem_centralizer_iff.1 (hPc he) (x : G) hxX).symm
  have hxP : (x : G) ∉ P := by
    intro hxP
    have hxc : ∀ h ∈ X, h * (x : G) = (x : G) * h := fun h hh =>
      Subgroup.mem_centralizer_iff.1 (hPc hxP) h hh
    have hxO : (x : G) ∈ pCoreOf 2 X := by
      refine hX.2.1 ⟨hxX, ?_⟩
      show (x : G) ∈ Subgroup.centralizer (pCoreOf 2 X : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      exact hxc h (pCoreOf_le 2 X hh)
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 X) ⟨(x : G), hxO⟩
    have hdvd : orderOf (x : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hk)
    rw [hx'] at hdvd
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd
    omega
  obtain ⟨hE', hcard'⟩ := exists_elemAbelian_sup_zpowers hP hx' hcomm hxP
  have hle : P ⊔ Subgroup.zpowers (x : G) ≤ I :=
    sup_le hPI ((Subgroup.zpowers_le.2 (hXI hxX)))
  have h3r : 3 ≤ CFSG.Open.pRank 3 I :=
    le_pRank Nat.prime_three hle hE' (k := 3) (by rw [hcard', hP9]; norm_num)
  have htop : CFSG.Open.pRank 3 (⊤ : Subgroup ↥I) = CFSG.Open.pRank 3 I :=
    pRank_top_subtype (p := 3) I
  omega

end S15223

end CFSG.Quasithin
