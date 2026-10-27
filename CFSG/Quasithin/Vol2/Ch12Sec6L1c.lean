module

public import CFSG.Quasithin.Vol2.Ch12Sec6L1b
public import CFSG.Quasithin.H13.A7Nat1233LinCover
public import CFSG.Quasithin.Background.InternalSecAutOn

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b Equiv
open scoped IsMulCommutative

namespace S126L1c

@[expose] def bsw : Perm (Fin 8) := swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7

theorem bsw_inv : bsw⁻¹ = bsw := by
  decide

@[expose] def Q8 : Subgroup (Perm (Fin 8)) :=
  CFSG.QuasithinUnique.Claim2526.P8 ⊓ alternatingGroup (Fin 8)

@[expose] def g1 : Perm (Fin 8) := swap 0 1

@[expose] def g2 : Perm (Fin 8) := swap 0 2 * swap 1 3

theorem g1_mem : g1 ∈ CFSG.QuasithinUnique.Claim2526.P8 :=
  Subgroup.subset_closure (by simp [CFSG.QuasithinUnique.Claim2526.p8Gens, g1])

theorem g2_mem : g2 ∈ CFSG.QuasithinUnique.Claim2526.P8 :=
  Subgroup.subset_closure (by simp [CFSG.QuasithinUnique.Claim2526.p8Gens, g2])

theorem bsw_mem : bsw ∈ CFSG.QuasithinUnique.Claim2526.P8 :=
  Subgroup.subset_closure (by simp [CFSG.QuasithinUnique.Claim2526.p8Gens, bsw])

theorem tau20_eq : tau 2 0 = g2 := by
  decide

theorem tau10_eq : tau 1 0 = g1 * (g2 * g1 * g2⁻¹) := by
  decide

theorem tau01_eq : tau 0 1 = bsw * tau 1 0 * bsw⁻¹ := by
  decide

theorem tau02_eq : tau 0 2 = bsw * g2 * bsw⁻¹ := by
  decide

theorem sign_tau : ∀ u v : Fin 4, Equiv.Perm.sign (tau u v) = 1 := by
  decide

theorem tau_mem_A8 (u v : Fin 4) : tau u v ∈ alternatingGroup (Fin 8) :=
  Equiv.Perm.mem_alternatingGroup.2 (sign_tau u v)

theorem bsw_mem_A8 : bsw ∈ alternatingGroup (Fin 8) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem mem_Q8 : tau 1 0 ∈ Q8 ∧ tau 2 0 ∈ Q8 ∧ tau 0 1 ∈ Q8 ∧ tau 0 2 ∈ Q8 ∧ bsw ∈ Q8 := by
  have h10 : tau 1 0 ∈ CFSG.QuasithinUnique.Claim2526.P8 := by
    rw [tau10_eq]
    exact Subgroup.mul_mem _ g1_mem
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ g2_mem g1_mem) (Subgroup.inv_mem _ g2_mem))
  refine ⟨⟨h10, tau_mem_A8 1 0⟩, ⟨tau20_eq ▸ g2_mem, tau_mem_A8 2 0⟩, ⟨?_, tau_mem_A8 0 1⟩,
    ⟨?_, tau_mem_A8 0 2⟩, ⟨bsw_mem, bsw_mem_A8⟩⟩
  · rw [tau01_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ bsw_mem h10) (Subgroup.inv_mem _ bsw_mem)
  · rw [tau02_eq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ bsw_mem g2_mem) (Subgroup.inv_mem _ bsw_mem)

theorem card_Q8_le : Nat.card Q8 ≤ 64 := by
  have hdvd : Nat.card Q8 ∣ 2 ^ 7 := by
    rw [show (2 : ℕ) ^ 7 = 128 by norm_num, ← CFSG.QuasithinUnique.Claim2526.card_P8]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card Q8 ≠ 128 := by
    intro h
    have hle : CFSG.QuasithinUnique.Claim2526.P8 ≤ Q8 := by
      refine (Subgroup.eq_of_le_of_card_ge inf_le_left ?_).ge
      rw [CFSG.QuasithinUnique.Claim2526.card_P8]
      exact h.ge
    have h1 : g1 ∈ alternatingGroup (Fin 8) := (hle g1_mem).2
    rw [Equiv.Perm.mem_alternatingGroup, g1, Equiv.Perm.sign_swap (by decide)] at h1
    exact absurd h1 (by decide)
  obtain ⟨i, hi, hQ⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [hQ] at hne ⊢
  have hi6 : i ≤ 6 := by
    by_contra hc
    have : i = 7 := by omega
    subst this
    exact hne (by norm_num)
  calc 2 ^ i ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hi6
    _ = 64 := by norm_num

theorem fix_chk : ∀ x : Fin 8 → ZMod 2, (∀ i, x (tf 1 0 i) = x i) → (∀ i, x (tf 2 0 i) = x i) →
    (∀ i, x (tf 0 1 i) = x i) → (∀ i, x (tf 0 2 i) = x i) → (∀ i, x (bsw i) = x i) →
    ∀ i, x i = x 0 := by
  decide +kernel

theorem fix_of_coreAct {σ : Perm (Fin 8)} {m : ↥(coreMod 8)} (h : coreAct 8 σ m = m) (i : Fin 8) :
    Multiplicative.toAdd (m : PermMod 8) (σ⁻¹ i) = Multiplicative.toAdd (m : PermMod 8) i := by
  have h1 := congrArg (fun x : ↥(coreMod 8) =>
    (Multiplicative.toAdd (x : PermMod 8) : Fin 8 → ZMod 2) i) h
  simp only [coreAct_coe, permAct_apply] at h1
  exact h1

theorem eq_of_fix_Q8 {m : ↥(coreMod 8)} (h : ∀ σ ∈ Q8, coreAct 8 σ m = m) :
    m = 1 ∨ (m : PermMod 8) = allOnes 8 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mem_Q8
  have key := fix_chk (Multiplicative.toAdd (m : PermMod 8))
    (fun i => by rw [← tau_inv_apply]; exact fix_of_coreAct (h _ h1) i)
    (fun i => by rw [← tau_inv_apply]; exact fix_of_coreAct (h _ h2) i)
    (fun i => by rw [← tau_inv_apply]; exact fix_of_coreAct (h _ h3) i)
    (fun i => by rw [← tau_inv_apply]; exact fix_of_coreAct (h _ h4) i)
    (fun i => by
      have := fix_of_coreAct (h _ h5) i
      rwa [bsw_inv] at this)
  rcases zmod2_cases (Multiplicative.toAdd (m : PermMod 8) 0) with h0 | h0
  · left
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    funext i
    rw [key i, h0]
    rfl
  · right
    apply Multiplicative.toAdd.injective
    funext i
    rw [key i, h0]
    rfl

theorem coreAct_allOnes (τ : Perm (Fin 8)) {m : ↥(coreMod 8)} (hm : (m : PermMod 8) = allOnes 8) :
    coreAct 8 τ m = m := by
  apply Subtype.ext
  rw [coreAct_coe, hm, permAct_allOnes]

theorem fix_eq_of_sylow {P : Subgroup (Perm (Fin 8))} (hPA : P ≤ alternatingGroup (Fin 8))
    (hP2 : IsPGroup 2 P) (hP64 : 64 ≤ Nat.card P) {m : ↥(coreMod 8)}
    (h : ∀ σ ∈ P, coreAct 8 σ m = m) : ∀ τ : Perm (Fin 8), coreAct 8 τ m = m := by
  obtain ⟨g, hg⟩ := S126Ex.exists_conj_le_P8 hP2
  let P' := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hP'le : P' ≤ Q8 := by
    rintro _ ⟨q, hq, rfl⟩
    have e : (MulAut.conj g⁻¹).toMonoidHom q = g⁻¹ * q * g := by
      simp
    rw [e]
    refine ⟨hg q hq, ?_⟩
    have hn : (alternatingGroup (Fin 8)).Normal := inferInstance
    have := hn.conj_mem q (hPA hq) g⁻¹
    rwa [inv_inv] at this
  have hcard : Nat.card P' = Nat.card P :=
    Nat.card_congr (Subgroup.equivMapOfInjective P _ (MulAut.conj g⁻¹).injective).toEquiv.symm
  have hP'eq : P' = Q8 := Subgroup.eq_of_le_of_card_ge hP'le (by
    have := card_Q8_le
    omega)
  set y := coreAct 8 g⁻¹ m with hy
  have hfix : ∀ ρ ∈ Q8, coreAct 8 ρ y = y := by
    intro ρ hρ
    rw [← hP'eq] at hρ
    obtain ⟨q, hq, rfl⟩ := hρ
    have e : (MulAut.conj g⁻¹).toMonoidHom q = g⁻¹ * q * g := by
      simp
    rw [e, hy, ← MulAut.mul_apply, ← map_mul, show g⁻¹ * q * g * g⁻¹ = g⁻¹ * q by group, map_mul,
      MulAut.mul_apply, h q hq]
  have hm : m = coreAct 8 g y := by
    rw [hy, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  intro τ
  rcases eq_of_fix_Q8 hfix with h1 | h1
  · rw [hm, h1, map_one, map_one]
  · have hm' : (m : PermMod 8) = allOnes 8 := by
      rw [hm, coreAct_coe, h1, permAct_allOnes]
    exact coreAct_allOnes τ hm'

theorem commOf_top_eq {W : Type*} [CommGroup W] (X : Subgroup (MulAut W)) :
    XMod.commOf ↥X (⊤ : Subgroup W) = commV X := by
  unfold XMod.commOf commV
  congr 1
  ext w
  constructor
  · rintro ⟨a, l, -, rfl⟩
    exact ⟨a, a.2, l, rfl⟩
  · rintro ⟨x, hx, u, rfl⟩
    exact ⟨⟨x, hx⟩, u, Subgroup.mem_top _, rfl⟩

variable {G : Type} [Group G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem card_of_isSylowTwoOf {Γ : Type} [Group Γ] [Finite Γ] {S H : Subgroup Γ}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S H) {a m : ℕ} (hH : Nat.card H = 2 ^ a * m)
    (hm : ¬ 2 ∣ m) : Nat.card S = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hS.2.1.exists_card_eq
  have h1 : S.relIndex H * Nat.card S = Nat.card H := by
    have := Subgroup.relIndex_mul_card (H := S) (K := H)
    rwa [inf_of_le_left hS.1] at this
  have hodd : ¬ 2 ∣ S.relIndex H := hS.2.2
  rw [hH, hk] at h1
  rw [hk]
  generalize S.relIndex H = i at h1 hodd
  have hk1 : k ≤ a := by
    have hd : 2 ^ k ∣ 2 ^ a * m := ⟨i, by rw [← h1, mul_comm]⟩
    have hc : Nat.Coprime (2 ^ k) m :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_right hd)
  have hk2 : a ≤ k := by
    have hd : 2 ^ a ∣ i * 2 ^ k := ⟨m, h1⟩
    have hc : Nat.Coprime (2 ^ a) i :=
      Nat.Coprime.pow_left a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hodd)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_left hd)
  rw [show k = a by omega]

omit [IsMulCommutative ↥V] in
theorem card_ge_three [Finite G] {K : Subgroup G} {x y : G} (hx : x ∈ K) (hy : y ∈ K) (hx1 : x ≠ 1)
    (hy1 : y ≠ 1) (hxy : x ≠ y) : 3 ≤ Nat.card K := by
  have hsub : ({1, x, y} : Set G) ⊆ (K : Set G) := by
    intro z hz
    rcases hz with rfl | rfl | rfl
    · exact K.one_mem
    · exact hx
    · exact hy
  have h3 : ({1, x, y} : Set G).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, x, y, hx1.symm, hy1.symm, hxy, rfl⟩
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3] at this
  rw [← Nat.card_coe_set_eq] at this
  exact this

omit [IsMulCommutative ↥V] in
theorem card_autOn [Finite G] (hH : Hyp126 G T L V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(autOn L V) = Nat.card ↥(alternatingGroup (Fin 8)) := by
  obtain ⟨φ, hφ, hker⟩ := hH.alt8
  have hk : (InternalSec.autOnHom hLV).ker = φ.ker := by
    rw [hker]
    ext l
    rw [InternalSec.mem_ker_autOnHom, Subgroup.mem_subgroupOf]
  rw [← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (InternalSec.autOnHom_surjective hLV)).toEquiv,
    ← Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv]
  exact Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hk).toEquiv

omit [IsMulCommutative ↥V] in
theorem part2 [Finite G] (h1222 : Stmt12_2_2) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥) :
    Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 ∧
      V ⊓ Subgroup.centralizer (L : Set G) = V ⊓ Subgroup.centralizer (T : Set G) := by
  have hyp := hH.hyp
  rcases h1222 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow with hAlt | h3
  · exact absurd hAlt hyp.notAlt
  obtain ⟨-, -, hall⟩ := h3 L hyp.maximal hyp.faithful hyp.quasisimple
  obtain ⟨⟨hVT, hTV, hred, -⟩, -, -, -⟩ := hall V hyp.irrPlus
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hyp.irrPlus.2.2.1
  have hVL : ⁅V, L⁆ = V := hyp.irrPlus.2.2.2.1
  have hTL := hyp.normalizes
  have hVe : IsElemAbelian 2 V := isElemAbelian_of_reduced (hVT.trans le_sup_right) hred
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hVe.2 v v.2)
  obtain ⟨hc, hmod⟩ := hH.module
  set Z : Subgroup ↥V := (Subgroup.centralizer (L : Set G)).subgroupOf V with hZdef
  have hZfix : Z ≤ fixV (autOn L V) := InternalSec.le_fixV_autOn inf_le_right
  have hcomm : commV (autOn L V) = ⊤ := InternalSec.commV_autOn_eq_top hLV hVL
  have hZcard : Nat.card Z = Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) := by
    have e : Z = (V ⊓ Subgroup.centralizer (L : Set G)).subgroupOf V := by
      rw [hZdef, Subgroup.inf_subgroupOf_left]
    rw [e]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hZ1 : Z ≠ ⊥ := by
    intro h
    apply hZ
    rw [← Subgroup.card_eq_one, ← hZcard, h, Subgroup.card_bot]
  have h2 : Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = 2 := by
    rcases VolI.altNaturalCoverEight_holds ↥V hV2 (autOn L V) Z hZfix hcomm hmod with h | h
    · exact absurd h hZ1
    · rw [← hZcard]
      exact h.1
  refine ⟨h2, le_antisymm ?_ ?_⟩
  · intro z hz
    refine ⟨hz.1, Subgroup.mem_centralizer_iff.2 fun t ht => ?_⟩
    have hzt : t * z * t⁻¹ ∈ V ⊓ Subgroup.centralizer (L : Set G) := by
      refine ⟨(Subgroup.mem_normalizer_iff.1 (hTV ht) z).1 hz.1,
        Subgroup.mem_centralizer_iff.2 fun l hl => ?_⟩
      have hl' : t⁻¹ * l * t ∈ L := by
        have := (Subgroup.mem_normalizer_iff.1 (hTL (T.inv_mem ht)) l).1 hl
        simpa using this
      have h1 := Subgroup.mem_centralizer_iff.1 hz.2 _ hl'
      calc l * (t * z * t⁻¹) = t * ((t⁻¹ * l * t) * z) * t⁻¹ := by group
        _ = t * (z * (t⁻¹ * l * t)) * t⁻¹ := by rw [h1]
        _ = t * z * t⁻¹ * l := by group
    by_cases hz1 : z = 1
    · rw [hz1, mul_one, one_mul]
    have hzt1 : t * z * t⁻¹ ≠ 1 := fun h => hz1 (by
      calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
        _ = 1 := by rw [h]; group)
    by_contra hne
    have hne' : t * z * t⁻¹ ≠ z := fun h => hne (by
      calc t * z = t * z * t⁻¹ * t := by group
        _ = z * t := by rw [h])
    have := card_ge_three hzt hz hzt1 hz1 hne'
    omega
  · intro v hv
    refine Subgroup.mem_inf.2 ⟨hv.1, ?_⟩
    have hU : XMod.commOf ↥(autOn L V) (⊤ : Subgroup ↥V) = ⊤ := by
      rw [commOf_top_eq, hcomm]
    obtain ⟨π', Φ, hπ's, hΦ⟩ := A7.LinCover.exists_mulEquiv_coreMod_eight hV2 hmod hZfix hU hZ1
    have hcardA := card_autOn hH hLV
    have hπ'i : Function.Injective π' := by
      obtain ⟨e⟩ := Finite.card_eq.1 hcardA.symm
      exact (Finite.injective_iff_surjective_of_equiv e).2 hπ's
    let f : ↥(alternatingGroup (Fin 8)) →* MulAut ↥V := (autOn L V).subtype.comp π'
    have hfi : Function.Injective f := Subtype.val_injective.comp hπ'i
    have hfr : f.range = autOn L V := by
      ext x
      constructor
      · rintro ⟨σ, rfl⟩
        exact (π' σ).2
      · intro hx
        obtain ⟨σ, hσ⟩ := hπ's ⟨x, hx⟩
        exact ⟨σ, by simp [f, hσ]⟩
    have hsylTL : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
      A4.isSylowTwoOf_inf_normal
        (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow (le_sup_right : T ≤ L ⊔ T)) le_sup_left
        (sup_le Subgroup.le_normalizer hTL)
    have hS := CFSG.QuasithinUnique.Setup.isSylowTwoOf_autOn hsylTL hLV
    have hS64 : Nat.card ↥(autOn (T ⊓ L) V) = 2 ^ 6 :=
      card_of_isSylowTwoOf hS (m := 315) (by rw [hcardA, card_A8]; norm_num) (by decide)
    let P₀ : Subgroup ↥(alternatingGroup (Fin 8)) := (autOn (T ⊓ L) V).comap f
    have hP₀ : Nat.card P₀ = 64 := by
      have h1 : P₀.map f = autOn (T ⊓ L) V := by
        rw [Subgroup.map_comap_eq, hfr]
        exact inf_of_le_right hS.1
      have h2 : Nat.card (P₀.map f) = Nat.card P₀ :=
        Nat.card_congr (Subgroup.equivMapOfInjective P₀ f hfi).toEquiv.symm
      rw [← h2, h1, hS64]
      norm_num
    let P : Subgroup (Perm (Fin 8)) := P₀.map (alternatingGroup (Fin 8)).subtype
    have hP : Nat.card P = 64 := by
      rw [← hP₀]
      exact Nat.card_congr (Subgroup.equivMapOfInjective P₀ _ Subtype.val_injective).toEquiv.symm
    have hPA : P ≤ alternatingGroup (Fin 8) := Subgroup.map_subtype_le _
    have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 6) (by rw [hP]; norm_num)
    let v' : ↥(⊤ : Subgroup ↥V) := ⟨⟨v, hv.1⟩, Subgroup.mem_top _⟩
    have hfixP : ∀ σ ∈ P, coreAct 8 σ (Φ v') = Φ v' := by
      rintro _ ⟨σ, hσ, rfl⟩
      obtain ⟨t, ht, htTL, hta⟩ := mem_autOn_iff_exists.mp (show f σ ∈ autOn (T ⊓ L) V from hσ)
      have hvt : ((π' σ : ↥(autOn L V)) : MulAut ↥V) ⟨v, hv.1⟩ = ⟨v, hv.1⟩ := by
        have e1 : ((π' σ : ↥(autOn L V)) : MulAut ↥V) = conjAct V ⟨t, ht⟩ := hta.symm
        rw [e1]
        apply Subtype.ext
        change t * v * t⁻¹ = v
        rw [Subgroup.mem_centralizer_iff.1 hv.2 t htTL.1, mul_inv_cancel_right]
      have h1 := hΦ σ v' (by rw [hvt]; exact Subgroup.mem_top _)
      have e2 : (⟨((π' σ : ↥(autOn L V)) : MulAut ↥V) v', by rw [hvt]; exact Subgroup.mem_top _⟩ :
          ↥(⊤ : Subgroup ↥V)) = v' := Subtype.ext hvt
      rw [e2] at h1
      exact h1.symm
    have hfixA := fix_eq_of_sylow hPA hP2 hP.ge hfixP
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨σ, hσ⟩ := hπ's ⟨conjAct V ⟨l, hLV hl⟩, mem_autOn_iff_exists.mpr ⟨l, hLV hl, hl, rfl⟩⟩
    have hmem : ((π' σ : ↥(autOn L V)) : MulAut ↥V) v' ∈ (⊤ : Subgroup ↥V) := Subgroup.mem_top _
    have h1 := hΦ σ v' hmem
    rw [show VolI.act8 σ (Φ v') = coreAct 8 σ (Φ v') from rfl, hfixA] at h1
    have h2 := congrArg (fun x : ↥(⊤ : Subgroup ↥V) => ((x : ↥V) : G)) (Φ.injective h1)
    simp only at h2
    rw [hσ] at h2
    change l * v * l⁻¹ = v at h2
    calc l * v = l * v * l⁻¹ * l := by group
      _ = v * l := by rw [h2]

end S126L1c

end CFSG.Quasithin.H13
