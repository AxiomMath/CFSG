module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec48U4qDefs
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBModuleAbstract
public import CFSG.LocalAnalysis.EvenBN.Common.FongSeitzFourB
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
  CFSG.Quasithin.F6.GoldAmL3T

open scoped Pointwise commutatorElement

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

private theorem Q_comm {X : Setup Γ G} {i : ℤ} (hQ : IsElemAbelian 2 (X.Q i))
    {a b : G} (ha : a ∈ X.Q i) (hb : b ∈ X.Q i) : a * b = b * a := by
  letI : IsMulCommutative ↥(X.Q i) := hQ.1
  have h := mul_comm' (⟨a, ha⟩ : ↥(X.Q i)) (⟨b, hb⟩ : ↥(X.Q i))
  simpa using congrArg Subtype.val h

private theorem C_L_Q_eq_Q (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G)) (i : ℤ)
    (hQ : IsElemAbelian 2 (X.Q i)) :
    X.L i ⊓ Subgroup.centralizer (X.Q i : Set G) = X.Q i := by
  refine le_antisymm ?_ ?_
  · intro x hx
    exact hc (X.vert i) ⟨X.L_le_Gi i hx.1, hx.2⟩
  · intro x hx
    refine Subgroup.mem_inf.mpr ⟨X.Q_le_L i hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Q_comm hQ hx hy).symm

private theorem action_eq_one_of_card_lt {X : Setup Γ G} {i : ℤ} {W : Type*} [Group W]
    [Finite W] {d : ℕ} (hn : 2 ≤ X.n i) (hW : Nat.card W = 2 ^ d) (hd : d < 2 * X.n i)
    (ρ : ↥(X.L i) →* MulAut W)
    (hQtriv : ∀ x : ↥(X.L i), (x : G) ∈ X.Q i → ρ x = 1) : ρ = 1 := by
  classical
  let L := X.L i
  let F := GaloisField 2 (X.n i)
  haveI : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L) (X.L_le_Gi i)
  have hpc : pCoreOf 2 L = X.Q i := (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq
  have hker : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    exact hQtriv x (by
      rw [← hpc]
      exact (CFSG.mem_openPCoreOf_iff x).mpr hx)
  let ρbar : (↥L ⧸ CFSG.pCore 2 ↥L) →* MulAut W := QuotientGroup.lift _ ρ hker
  obtain ⟨e0⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e0.trans (CFSG.Quasithin.pslTwoGf2EquivSl (X.n i))
  let ρ' : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut W := ρbar.comp e.symm.toMonoidHom
  have hρ' : ρ' = 1 := by
    refine CFSG.LocalAnalysis.EvenBN.Common.sl2_eq_one_of_card_lt
      (X := Matrix.SpecialLinearGroup (Fin 2) F) (V := W) (e := MulEquiv.refl _)
      ?_ hn ρ' hW hd
    exact GaloisField.card 2 (X.n i) (by omega)
  have hbar : ρbar = 1 := by
    ext y w
    have h1 : (ρ' (e y)) w = w := by rw [hρ']; rfl
    simpa [ρ', e] using h1
  ext x w
  have h1 : (ρbar (QuotientGroup.mk' (CFSG.pCore 2 ↥L) x)) w = w := by rw [hbar]; rfl
  change (ρ x) w = w at h1
  simpa using h1

private theorem conjAction_ker_eq_Q (X : Setup Γ G) (i : ℤ)
    (hQ : IsElemAbelian 2 (X.Q i))
    (hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G))
    (hCeq : X.L i ⊓ Subgroup.centralizer (X.Q i : Set G) = X.Q i) :
    (CFSG.SL2MinimalFaithful.conjAction hLQ).ker = (X.Q i).subgroupOf (X.L i) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    have hxcent : (x : G) ∈ Subgroup.centralizer (X.Q i : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have h1 := congrArg (fun φ : MulAut ↥(X.Q i) => ((φ ⟨q, hq⟩ : ↥(X.Q i)) : G)) hx
      rw [CFSG.SL2MinimalFaithful.conjAction_apply, MulAut.one_apply] at h1
      have h2 : (x : G) * q * (x : G)⁻¹ = q := by simpa using h1
      calc q * (x : G) = ((x : G) * q * (x : G)⁻¹) * (x : G) := by rw [h2]
        _ = (x : G) * q := by group
    have hx' : (x : G) ∈ X.L i ⊓ Subgroup.centralizer (X.Q i : Set G) := ⟨x.2, hxcent⟩
    rwa [hCeq] at hx'
  · intro hx
    ext q
    rw [CFSG.SL2MinimalFaithful.conjAction_apply, MulAut.one_apply]
    have hcomm := Q_comm hQ hx q.2
    calc (x : G) * (q : G) * (x : G)⁻¹ = (q : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
      _ = (q : G) := by group

theorem two_mul_n_le_of_isElemAbelian (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (i : ℤ) (hn : 2 ≤ X.n i) (hQ : IsElemAbelian 2 (X.Q i)) {d : ℕ}
    (hd : Nat.card (X.Q i) = 2 ^ d) : 2 * X.n i ≤ d := by
  classical
  let L := X.L i
  let Q := X.Q i
  let F := GaloisField 2 (X.n i)
  haveI : Finite ↥Q := finite_of_le_stabilizer X.hyp (H := Q) (X.Q_le_Gi i)
  haveI : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L) (X.L_le_Gi i)
  have hpc : pCoreOf 2 L = Q := (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hpc]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) L
  let ρ : ↥L →* MulAut ↥Q := CFSG.SL2MinimalFaithful.conjAction hLQ
  have hCeq : L ⊓ Subgroup.centralizer (Q : Set G) = Q := C_L_Q_eq_Q X hc i hQ
  have hker : ρ.ker = Q.subgroupOf L :=
    conjAction_ker_eq_Q X i hQ hLQ hCeq
  have hker_le : CFSG.pCore 2 ↥L ≤ ρ.ker := by
    rw [hker, ← hpc, CFSG.openPCoreOf_subgroupOf]
  let ρbar : (↥L ⧸ CFSG.pCore 2 ↥L) →* MulAut ↥Q := QuotientGroup.lift _ ρ hker_le
  have hinj : Function.Injective ρbar := by
    rw [← MonoidHom.ker_eq_bot_iff]
    ext y
    rw [Subgroup.mem_bot, MonoidHom.mem_ker]
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) y
      have hx : x ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        simpa [ρbar, QuotientGroup.lift_mk] using hy
      rw [hker] at hx
      have hxQ : (x : G) ∈ Q := hx
      have hxpc : x ∈ CFSG.pCore 2 ↥L := by
        rw [← CFSG.openPCoreOf_subgroupOf 2 L, hpc]
        exact Subgroup.mem_subgroupOf.mpr hxQ
      exact (QuotientGroup.eq_one_iff x).mpr hxpc
    · intro hy
      rw [hy, map_one]
  obtain ⟨e0⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert i)).quot
  let e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
    e0.trans (CFSG.Quasithin.pslTwoGf2EquivSl (X.n i))
  let ρSL : Matrix.SpecialLinearGroup (Fin 2) F →* MulAut ↥Q := ρbar.comp e.symm.toMonoidHom
  have hinjSL : Function.Injective ρSL := hinj.comp e.symm.injective
  exact CFSG.LocalAnalysis.EvenBN.LinearThree.CaseBModule.two_mul_le_of_faithful
    hn (GaloisField.card 2 (X.n i) (by omega)) ρSL hinjSL hd

private theorem exists_card_eq_two_pow_lt (X : Setup Γ G) (i : ℤ)
    (hQ : IsElemAbelian 2 (X.Q i)) (hd : Nat.card (X.Q i) = 2 ^ (2 * X.n i))
    {N : Subgroup G} (hN : N ≤ X.Q i) (hbot : N ≠ ⊥) (htop : N ≠ X.Q i) :
    ∃ b : ℕ, Nat.card N = 2 ^ b ∧ 0 < b ∧ b < 2 * X.n i := by
  haveI : Finite ↥N := finite_of_le_stabilizer X.hyp (H := N) (hN.trans (X.Q_le_Gi i))
  haveI : Finite ↥(X.Q i) := finite_of_le_stabilizer X.hyp (H := X.Q i) (X.Q_le_Gi i)
  have hQp : IsPGroup 2 (X.Q i) := CFSG.LocalAnalysis.EvenBN.Common.isPGroup_two_of_mul_self
    (fun v hv => by simpa [pow_two] using hQ.2 v hv)
  have hNp : IsPGroup 2 ↥N := hQp.to_le hN
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hNp
  have hbpos : 0 < b := by
    rcases Nat.eq_zero_or_pos b with rfl | h
    · exfalso
      exact hbot ((Subgroup.card_eq_one).1 (by rw [hb, pow_zero]))
    · exact h
  have hblt : b < 2 * X.n i := by
    by_contra hle
    have hbg : 2 * X.n i ≤ b := by omega
    have hcardle : Nat.card (X.Q i) ≤ Nat.card N := by
      rw [hd, hb]
      exact Nat.pow_le_pow_right (by norm_num) hbg
    exact htop (Subgroup.eq_of_le_of_card_ge hN hcardle)
  exact ⟨b, hb, hbpos, hblt⟩

private theorem le_centralizer_of_card_lt (X : Setup Γ G) (i : ℤ) (hn : 2 ≤ X.n i)
    (hQ : IsElemAbelian 2 (X.Q i)) {b : ℕ} {N : Subgroup G} (hN : N ≤ X.Q i)
    (hL : X.L i ≤ Subgroup.normalizer (N : Set G)) (hb : Nat.card N = 2 ^ b)
    (hblt : b < 2 * X.n i) : X.L i ≤ Subgroup.centralizer (N : Set G) := by
  haveI : Finite ↥N := finite_of_le_stabilizer X.hyp (H := N) (hN.trans (X.Q_le_Gi i))
  let ρN : ↥(X.L i) →* MulAut ↥N := CFSG.SL2MinimalFaithful.conjAction hL
  have hρN : ρN = 1 := by
    refine action_eq_one_of_card_lt (X := X) (i := i) hn hb hblt ρN ?_
    intro x hx
    ext n
    rw [CFSG.SL2MinimalFaithful.conjAction_apply, MulAut.one_apply]
    have hcomm := Q_comm hQ hx (hN n.2)
    calc (x : G) * (n : G) * (x : G)⁻¹ = (n : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
      _ = (n : G) := by group
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro n hnN
  have h1 : (x : G) * n * (x : G)⁻¹ = n := by
    have h2 : ((ρN ⟨x, hx⟩ ⟨n, hnN⟩ : ↥N) : G) = (n : G) := by rw [hρN]; rfl
    rw [CFSG.SL2MinimalFaithful.conjAction_apply] at h2
    simpa using h2
  calc n * (x : G) = ((x : G) * n * (x : G)⁻¹) * (x : G) := by rw [h1]
    _ = (x : G) * n := by group

private theorem subgroupOf_normal (X : Setup Γ G) (i : ℤ) (hQ : IsElemAbelian 2 (X.Q i))
    {N : Subgroup G} (hN : N ≤ X.Q i) : (N.subgroupOf (X.Q i)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have hcomm := Q_comm hQ (hN hn) g.2
  have hconj : ((g : G) * (n : G) * (g : G)⁻¹) = (n : G) := by
    calc (g : G) * (n : G) * (g : G)⁻¹ = (n : G) * (g : G) * (g : G)⁻¹ := by rw [hcomm]
      _ = (n : G) := by group
  change (g : G) * (n : G) * (g : G)⁻¹ ∈ N
  rw [hconj]
  exact hn

private theorem map_subgroupOf_conjAction (X : Setup Γ G) (i : ℤ)
    {N : Subgroup G} (hN : N ≤ X.Q i)
    (hL : X.L i ≤ Subgroup.normalizer (N : Set G))
    (hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G)) :
    ∀ j : ↥(X.L i), (N.subgroupOf (X.Q i)).map
      (CFSG.SL2MinimalFaithful.conjAction hLQ j : ↥(X.Q i) →* ↥(X.Q i)) =
      N.subgroupOf (X.Q i) := by
  intro j
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    have hx' : ((x : ↥(X.Q i)) : G) = (j : G) * (y : G) * (j : G)⁻¹ :=
      (congrArg Subtype.val hyx).symm.trans
        (CFSG.SL2MinimalFaithful.conjAction_apply hLQ j y)
    rw [hx']
    exact (Subgroup.mem_normalizer_iff.mp (hL j.2) (y : G)).mp hy
  · intro hx
    rw [Subgroup.mem_subgroupOf] at hx
    have hxj : (j : G)⁻¹ * (x : G) * (j : G) ∈ N := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hL (Subgroup.inv_mem _ j.2)) (x : G)).mp hx
    refine Subgroup.mem_map.mpr ⟨⟨(j : G)⁻¹ * (x : G) * (j : G), hN hxj⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hxj
    · apply Subtype.ext
      calc ((CFSG.SL2MinimalFaithful.conjAction hLQ j)
            ⟨(j : G)⁻¹ * (x : G) * (j : G), hN hxj⟩ : G)
          = (j : G) * ((j : G)⁻¹ * (x : G) * (j : G)) * (j : G)⁻¹ :=
            CFSG.SL2MinimalFaithful.conjAction_apply hLQ j _
        _ = (x : G) := by group

private theorem conj_mem_quotient_of_card_lt (X : Setup Γ G) (i : ℤ) (hn : 2 ≤ X.n i)
    (hQ : IsElemAbelian 2 (X.Q i)) {N : Subgroup G} (hN : N ≤ X.Q i)
    (hL : X.L i ≤ Subgroup.normalizer (N : Set G)) {b : ℕ}
    (hbpos : 0 < b) (hblt : b < 2 * X.n i)
    (hqcard : Nat.card (↥(X.Q i) ⧸ N.subgroupOf (X.Q i)) = 2 ^ (2 * X.n i - b))
    (hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G)) {k : G} (hkL : k ∈ X.L i)
    {q : G} (hq : q ∈ X.Q i) : k * q * k⁻¹ * q⁻¹ ∈ N := by
  classical
  haveI : Finite ↥N := finite_of_le_stabilizer X.hyp (H := N) (hN.trans (X.Q_le_Gi i))
  haveI : Finite ↥(X.Q i) := finite_of_le_stabilizer X.hyp (H := X.Q i) (X.Q_le_Gi i)
  let W : Subgroup ↥(X.Q i) := N.subgroupOf (X.Q i)
  haveI hWn : W.Normal := subgroupOf_normal X i hQ hN
  let ρQ : ↥(X.L i) →* MulAut ↥(X.Q i) := CFSG.SL2MinimalFaithful.conjAction hLQ
  have hWmap : ∀ j : ↥(X.L i), W.map (ρQ j : ↥(X.Q i) →* ↥(X.Q i)) = W := by
    intro j
    exact map_subgroupOf_conjAction X i hN hL hLQ j
  let ρQN : ↥(X.L i) →* MulAut (↥(X.Q i) ⧸ W) :=
    CFSG.SL2MinimalFaithful.quotientAction ρQ W hWmap
  have hρQN : ρQN = 1 := by
    refine action_eq_one_of_card_lt (X := X) (i := i) hn hqcard (by omega) ρQN ?_
    intro x hx
    have hρx : ρQ x = 1 := by
      ext q
      rw [CFSG.SL2MinimalFaithful.conjAction_apply, MulAut.one_apply]
      have hcomm := Q_comm hQ hx q.2
      calc (x : G) * (q : G) * (x : G)⁻¹ = (q : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
        _ = (q : G) := by group
    ext v
    induction v using QuotientGroup.induction_on with
    | H q =>
      show (CFSG.SL2MinimalFaithful.quotientAction ρQ W hWmap x)
        ((q : ↥(X.Q i)) : ↥(X.Q i) ⧸ W) = ((q : ↥(X.Q i)) : ↥(X.Q i) ⧸ W)
      rw [CFSG.SL2MinimalFaithful.quotientAction_mk, hρx, MulAut.one_apply]
  have hfix : ρQN ⟨k, hkL⟩ ((⟨q, hq⟩⁻¹ : ↥(X.Q i)) : ↥(X.Q i) ⧸ W) =
      ((⟨q, hq⟩⁻¹ : ↥(X.Q i)) : ↥(X.Q i) ⧸ W) := by
    rw [hρQN]; rfl
  rw [CFSG.SL2MinimalFaithful.quotientAction_mk, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at hfix
  change (((ρQ ⟨k, hkL⟩ (⟨q, hq⟩ : ↥(X.Q i))⁻¹ : ↥(X.Q i)) : G)⁻¹ *
    ((⟨q, hq⟩ : ↥(X.Q i))⁻¹ : G)) ∈ N at hfix
  rw [CFSG.SL2MinimalFaithful.conjAction_apply] at hfix
  change (k * (q : G)⁻¹ * k⁻¹)⁻¹ * (q : G)⁻¹ ∈ N at hfix
  have hconj : k * q * k⁻¹ * q⁻¹ = (k * q⁻¹ * k⁻¹)⁻¹ * q⁻¹ := by group
  rwa [hconj]

private theorem sq_mem_Q_of_le_centralizer (X : Setup Γ G) (i : ℤ)
    (hQ : IsElemAbelian 2 (X.Q i)) {N : Subgroup G} (hN : N ≤ X.Q i) {k : G}
    (hkL : k ∈ X.L i) (hcentN : ∀ n ∈ N, k * n * k⁻¹ = n)
    (hcommut : ∀ q : ↥(X.Q i), k * (q : G) * k⁻¹ * (q : G)⁻¹ ∈ N)
    (hCeq : X.L i ⊓ Subgroup.centralizer (X.Q i : Set G) = X.Q i) :
    k ^ 2 ∈ X.Q i := by
  have hk2cent : ∀ q : ↥(X.Q i), k ^ 2 * (q : G) * (k ^ 2)⁻¹ = (q : G) := by
    intro q
    set c : G := k * (q : G) * k⁻¹ * (q : G)⁻¹ with hcdef
    have hcN : c ∈ N := hcommut q
    have hcq : k * (q : G) * k⁻¹ = c * (q : G) := by rw [hcdef]; group
    have hck : k * c * k⁻¹ = c := hcentN c hcN
    have hcQ : c ∈ X.Q i := hN hcN
    have hc2 : c ^ 2 = 1 := hQ.2 c hcQ
    rw [pow_two]
    calc (k * k) * (q : G) * (k * k)⁻¹
        = k * (k * (q : G) * k⁻¹) * k⁻¹ := by group
      _ = k * (c * (q : G)) * k⁻¹ := by rw [hcq]
      _ = (k * c * k⁻¹) * (k * (q : G) * k⁻¹) := by group
      _ = c * (c * (q : G)) := by rw [hck, hcq]
      _ = c ^ 2 * (q : G) := by rw [pow_two]; group
      _ = (q : G) := by rw [hc2]; group
  have hk2L : k ^ 2 ∈ X.L i := (X.L i).pow_mem hkL 2
  have hk2cent' : k ^ 2 ∈ Subgroup.centralizer (X.Q i : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h := hk2cent ⟨q, hq⟩
    calc q * k ^ 2 = (k ^ 2 * q * (k ^ 2)⁻¹) * k ^ 2 := by rw [h]
      _ = k ^ 2 * q := by group
  rw [← hCeq]
  exact Subgroup.mem_inf.mpr ⟨hk2L, hk2cent'⟩

private theorem eq_one_of_sq_mem (X : Setup Γ G) (i : ℤ) (hn : 2 ≤ X.n i)
    (hQ : IsElemAbelian 2 (X.Q i)) {k : G} (hkKi : k ∈ X.Ki i)
    (hk2Q : k ^ 2 ∈ X.Q i) : k = 1 := by
  haveI : Finite ↥(X.Q i) := finite_of_le_stabilizer X.hyp (H := X.Q i) (X.Q_le_Gi i)
  have hQp : IsPGroup 2 (X.Q i) := CFSG.LocalAnalysis.EvenBN.Common.isPGroup_two_of_mul_self
    (fun v hv => by simpa [pow_two] using hQ.2 v hv)
  have hordKi : orderOf k ∣ 2 ^ X.n i - 1 := by
    have h := Subgroup.orderOf_dvd_natCard (X.Ki i) hkKi
    rwa [X.card_Ki i] at h
  have hodd : Odd (2 ^ X.n i - 1) := by
    have h2 : 2 ^ X.n i = 2 * 2 ^ (X.n i - 1) := by
      calc 2 ^ X.n i = 2 ^ (X.n i - 1 + 1) := by rw [Nat.sub_one_add_one (by omega : X.n i ≠ 0)]
        _ = 2 ^ (X.n i - 1) * 2 := pow_succ _ _
        _ = 2 * 2 ^ (X.n i - 1) := by ring
    refine ⟨2 ^ (X.n i - 1) - 1, ?_⟩
    rw [h2]
    have hpos : 1 ≤ 2 ^ (X.n i - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hcop : Nat.Coprime 2 (2 ^ X.n i - 1) := Nat.coprime_two_left.mpr hodd
  obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hQp) ⟨k ^ 2, hk2Q⟩
  have hk2ord : orderOf (k ^ 2) = 2 ^ m := by
    simpa using hm
  have hdvd : orderOf (k ^ 2) ∣ 2 ^ X.n i - 1 :=
    (orderOf_pow_dvd (n := 2) (x := k)).trans hordKi
  have hpowdvd : 2 ^ m ∣ 2 ^ X.n i - 1 := by
    rw [← hk2ord]; exact hdvd
  have hm0 : m = 0 := by
    by_contra hm0
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have h2dvd : 2 ∣ 2 ^ (j + 1) := by
      refine ⟨2 ^ j, ?_⟩
      rw [pow_succ, mul_comm]
    have h2dvd' : 2 ∣ 2 ^ X.n i - 1 := h2dvd.trans hpowdvd
    have hnot2 : ¬ 2 ∣ 2 ^ X.n i - 1 := by
      rw [← even_iff_two_dvd]
      exact Nat.not_even_iff_odd.mpr hodd
    exact hnot2 h2dvd'
  have hk2 : k ^ 2 = 1 := by
    rw [← orderOf_eq_one_iff, hk2ord, hm0, pow_zero]
  have hdvd2 : orderOf k ∣ 2 := orderOf_dvd_of_pow_eq_one hk2
  have hgcd : orderOf k ∣ Nat.gcd 2 (2 ^ X.n i - 1) := Nat.dvd_gcd hdvd2 hordKi
  rw [hcop.gcd_eq_one] at hgcd
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)

theorem eq_bot_or_eq_Q_of_card (X : Setup Γ G) (hc : CharTwoStab (V := V) (G := G))
    (i : ℤ) (hn : 2 ≤ X.n i) (hQ : IsElemAbelian 2 (X.Q i))
    (hd : Nat.card (X.Q i) = 2 ^ (2 * X.n i)) (N : Subgroup G) (hN : N ≤ X.Q i)
    (hL : X.L i ≤ Subgroup.normalizer (N : Set G)) : N = ⊥ ∨ N = X.Q i := by
  classical
  by_cases hbot : N = ⊥
  · exact Or.inl hbot
  by_cases htop : N = X.Q i
  · exact Or.inr htop
  exfalso
  let L := X.L i
  let Q := X.Q i
  haveI : Finite ↥Q := finite_of_le_stabilizer X.hyp (H := Q) (X.Q_le_Gi i)
  haveI : Finite ↥L := finite_of_le_stabilizer X.hyp (H := L) (X.L_le_Gi i)
  obtain ⟨b, hb, hbpos, hblt⟩ := exists_card_eq_two_pow_lt X i hQ hd hN hbot htop
  have hpc : pCoreOf 2 L = Q := (X.hyp.isLocL2_oTwoPrime (X.vert i)).pCoreOf_eq
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hpc]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) L
  obtain ⟨⟨k, hkKi⟩, hk1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (X.torus_ne_bot i hn)
  have hk1 : k ≠ 1 := fun h => hk1' (Subtype.ext h)
  have hkL : k ∈ L := hkKi.2
  have hcent : X.L i ≤ Subgroup.centralizer (N : Set G) :=
    le_centralizer_of_card_lt X i hn hQ hN hL hb hblt
  have hcentN : ∀ n ∈ N, k * n * k⁻¹ = n := by
    intro n hnN
    have hmem : k ∈ Subgroup.centralizer (N : Set G) := hcent hkL
    rw [Subgroup.mem_centralizer_iff] at hmem
    have hcomm := hmem n hnN
    calc k * n * k⁻¹ = (n * k) * k⁻¹ := by rw [← hcomm]
      _ = n := by group
  let W : Subgroup ↥Q := N.subgroupOf Q
  haveI hWn : W.Normal := subgroupOf_normal X i hQ hN
  have hWcard : Nat.card W = 2 ^ b := by
    rw [← hb]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv
  have hqcard : Nat.card (↥Q ⧸ W) = 2 ^ (2 * X.n i - b) := by
    have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup W
    rw [hd, hWcard] at hcard
    have hle : b ≤ 2 * X.n i := hblt.le
    have hpow : 2 ^ (2 * X.n i) = 2 ^ (2 * X.n i - b) * 2 ^ b := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hpow] at hcard
    exact (Nat.eq_of_mul_eq_mul_right (Nat.two_pow_pos b) hcard).symm
  have hcommut : ∀ q : ↥Q, k * (q : G) * k⁻¹ * (q : G)⁻¹ ∈ N := by
    intro q
    exact conj_mem_quotient_of_card_lt X i hn hQ hN hL hbpos hblt hqcard hLQ hkL q.2
  have hk2Q : k ^ 2 ∈ Q :=
    sq_mem_Q_of_le_centralizer X i hQ hN hkL hcentN hcommut (C_L_Q_eq_Q X hc i hQ)
  exact hk1 (eq_one_of_sq_mem X i hn hQ hkKi hk2Q)

namespace U4qBase

variable {X : Setup Γ G}

theorem n1_le_two_mul (B : X.U4qBase) : X.n 1 ≤ 2 * X.n 0 := by
  have h := two_mul_n_le_of_isElemAbelian X B.gen.hyp.char 1 (B.gen.hyp.two_le_n 1) B.elem_Q1
    (d := 2 * X.n 0 + X.n 1) B.card_Q1
  omega

theorem Q1_irred (B : X.U4qBase) (h : X.n 1 = 2 * X.n 0)
    (N : Subgroup G) (hN : N ≤ X.Q 1) (hL : X.L 1 ≤ Subgroup.normalizer (N : Set G)) :
    N = ⊥ ∨ N = X.Q 1 := by
  refine eq_bot_or_eq_Q_of_card X B.gen.hyp.char 1 (B.gen.hyp.two_le_n 1) B.elem_Q1 ?_ N hN hL
  rw [B.card_Q1]
  congr 1
  omega

end U4qBase

end Setup

end CFSG.Quasithin.St84

end
