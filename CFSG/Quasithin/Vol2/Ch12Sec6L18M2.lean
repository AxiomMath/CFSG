module

public import CFSG.Quasithin.Vol2.Ch12Sec6L18Stmt
public import CFSG.Quasithin.Vol2.Ch10SecQ3CK8D
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.EmptyFaithful.LRed4Setup
public import CFSG.Quasithin.Background.G64ProofBasic
public import CFSG.Quasithin.Vol2.Ch12Sec6L12a
public import CFSG.Quasithin.Vol2.Ch12Sec6L14b
public import CFSG.Quasithin.Vol2.KGFact12614NoFF

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 S126 S126L1a S126P S126E S126F
  S126L1b S126N S126T2 CFSG.LieType.BorelTits Equiv
open scoped IsMulCommutative Pointwise commutatorElement

namespace S126M2

theorem mul_inv_mem_of_five {D : Type*} [Group D] [Finite D] (W : Subgroup D) [W.Normal]
    (a : D →* D) (ha : W ≤ W.comap a) (h5 : ∀ d, a (a (a (a (a d)))) = d)
    (hW : Nat.card D ≤ 4 * Nat.card W) (d : D) : d * (a d)⁻¹ ∈ W := by
  classical
  set f : D ⧸ W →* D ⧸ W := QuotientGroup.map W W a ha with hf
  have hf5 : ∀ q, f (f (f (f (f q)))) = q := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x => simp only [hf, QuotientGroup.map_mk, h5]
  let e : Equiv.Perm (D ⧸ W) :=
    { toFun := f
      invFun := fun q => f (f (f (f q)))
      left_inv := fun q => hf5 q
      right_inv := fun q => hf5 q }
  have he5 : e ^ 5 = 1 := by
    ext q
    simp only [pow_succ, pow_zero, one_mul, Equiv.Perm.mul_apply, Equiv.Perm.one_apply]
    exact hf5 q
  have hQ : Nat.card (D ⧸ W) ≤ 4 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup W
    have hpos : 0 < Nat.card W := Nat.card_pos
    by_contra hc
    have : 5 * Nat.card W ≤ Nat.card (D ⧸ W) * Nat.card W :=
      Nat.mul_le_mul_right _ (by omega)
    omega
  have h1 : orderOf e ∣ 5 := orderOf_dvd_of_pow_eq_one he5
  have h2 : orderOf e ∣ 24 := by
    have h3 := orderOf_dvd_natCard e
    rw [Nat.card_perm] at h3
    exact h3.trans (Nat.factorial_dvd_factorial hQ)
  have h3 : orderOf e = 1 := Nat.eq_one_of_dvd_one (by simpa using Nat.dvd_gcd h1 h2)
  rw [orderOf_eq_one_iff] at h3
  have h4 : f (QuotientGroup.mk d) = QuotientGroup.mk d :=
    DFunLike.congr_fun h3 (QuotientGroup.mk d)
  rw [hf, QuotientGroup.map_mk, QuotientGroup.eq] at h4
  have h6 := ‹W.Normal›.conj_mem _ h4 d
  simpa [mul_assoc] using h6

@[expose] def prj : PermMod 8 →* Multiplicative (Fin 5 → ZMod 2) where
  toFun x := Multiplicative.ofAdd fun k => Multiplicative.toAdd x (![3, 4, 5, 6, 7] k)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] noncomputable def kap : D8 →* Multiplicative (Fin 5 → ZMod 2) := prj.comp iota

theorem prj_pe : ∀ k : Fin 5,
    prj (nrm ((pe 2 (![3, 4, 5, 6, 7] k) : ↥(coreMod 8)) : PermMod 8)) =
      Multiplicative.ofAdd (Pi.single k 1) := by
  decide +kernel

theorem kap_pe (k : Fin 5) :
    kap (QuotientGroup.mk (pe 2 (![3, 4, 5, 6, 7] k))) = Multiplicative.ofAdd (Pi.single k 1) :=
  prj_pe k

theorem le_card_of_pe_mem (H : Subgroup D8)
    (h : ∀ k : Fin 5, (QuotientGroup.mk (pe 2 (![3, 4, 5, 6, 7] k)) : D8) ∈ H) :
    32 ≤ Nat.card H := by
  classical
  have htop : H.map kap = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have hz : z = ∏ k : Fin 5, Multiplicative.ofAdd (Pi.single k (Multiplicative.toAdd z k)) := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_prod]
      simp only [toAdd_ofAdd]
      exact (Finset.univ_sum_single _).symm
    rw [hz]
    refine Subgroup.prod_mem _ fun k _ => ?_
    rcases zmod2_cases (Multiplicative.toAdd z k) with h0 | h1
    · rw [h0, Pi.single_zero, ofAdd_zero]
      exact Subgroup.one_mem _
    · rw [h1, ← kap_pe k]
      exact ⟨_, h k, rfl⟩
  have h1 : Nat.card ↥(H.map kap) ≤ Nat.card H :=
    Nat.card_le_card_of_surjective _ (kap.subgroupMap_surjective H)
  rw [htop, Subgroup.card_top] at h1
  simpa [Nat.card_eq_fintype_card] using h1

@[expose] def c5 : Perm (Fin 8) := swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6

@[expose] def d5 : Perm (Fin 8) := swap 2 7 * swap 7 3 * swap 3 4 * swap 4 5

@[expose] def s5 : Fin 5 → Perm (Fin 8) := ![c5, c5 ^ 2, c5 ^ 3, c5 ^ 4, d5]

theorem c5_mem : c5 ∈ S126T2.A6s := by
  rw [S126T2.mem_A6s]
  refine ⟨by decide, by decide, ?_⟩
  rw [Perm.mem_alternatingGroup, c5, map_mul, map_mul, map_mul,
    Perm.sign_swap (show (2 : Fin 8) ≠ 3 by decide),
    Perm.sign_swap (show (3 : Fin 8) ≠ 4 by decide),
    Perm.sign_swap (show (4 : Fin 8) ≠ 5 by decide),
    Perm.sign_swap (show (5 : Fin 8) ≠ 6 by decide)]
  rfl

theorem d5_mem : d5 ∈ S126T2.A6s := by
  rw [S126T2.mem_A6s]
  refine ⟨by decide, by decide, ?_⟩
  rw [Perm.mem_alternatingGroup, d5, map_mul, map_mul, map_mul,
    Perm.sign_swap (show (2 : Fin 8) ≠ 7 by decide),
    Perm.sign_swap (show (7 : Fin 8) ≠ 3 by decide),
    Perm.sign_swap (show (3 : Fin 8) ≠ 4 by decide),
    Perm.sign_swap (show (4 : Fin 8) ≠ 5 by decide)]
  rfl

theorem s5_mem (k : Fin 5) : s5 k ∈ S126T2.A6s := by
  fin_cases k
  · exact c5_mem
  · exact S126T2.A6s.pow_mem c5_mem 2
  · exact S126T2.A6s.pow_mem c5_mem 3
  · exact S126T2.A6s.pow_mem c5_mem 4
  · exact d5_mem

theorem s5_pow : ∀ k : Fin 5, s5 k ^ 5 = 1 := by decide +kernel

theorem s5_zero : ∀ k : Fin 5, s5 k 0 = 0 := by decide +kernel

theorem s5_two : ∀ k : Fin 5, s5 k 2 = ![3, 4, 5, 6, 7] k := by decide +kernel

theorem altD8_ker :
    (Subgroup.zpowers (allOnes 8) ⊓ coreMod 8).subgroupOf (coreMod 8) = natKer 8 := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => h.1, fun h => ⟨h, x.2⟩⟩

theorem exists_D8_of_alternatingNatural {W : Type*} [CommGroup W] {Λ : Subgroup (MulAut W)}
    {U Z : Subgroup W} (h : AlternatingNatural Λ U Z 8) :
    ∃ π : ↥(alternatingGroup (Fin 8)) →* ↥Λ, Function.Surjective π ∧
      ∃ hU : (∀ a : ↥Λ, ∀ u ∈ U, (a : MulAut W) u ∈ U), ∃ β : ↥U →* D8,
        (∀ u : ↥U, β u = 1 ↔ (u : W) ∈ Z) ∧
        ∀ (γ : ↥(alternatingGroup (Fin 8))) (u : ↥U),
          β ⟨((π γ : ↥Λ) : MulAut W) u, hU (π γ) u u.2⟩ = dAct (γ : Perm (Fin 8)) (β u) := by
  obtain ⟨π, hπs, -, -, hUinv, -, -, -, β, -, hβk, hβeq⟩ := h
  let π₀ : ↥(alternatingGroup (Fin 8)) →* ↥Λ := π
  let β₀ : ↥U →* ↥(coreMod 8) ⧸ (Subgroup.zpowers (allOnes 8) ⊓ coreMod 8).subgroupOf (coreMod 8) :=
    β
  have hβk₀ : ∀ u : ↥U, β₀ u = 1 ↔ (u : W) ∈ Z := hβk
  have hβeq₀ : ∀ (γ : ↥(alternatingGroup (Fin 8))) (u : ↥U) (m : ↥(coreMod 8))
      (hu : ((π₀ γ : ↥Λ) : MulAut W) (u : W) ∈ U), β₀ u = QuotientGroup.mk m →
        β₀ ⟨((π₀ γ : ↥Λ) : MulAut W) (u : W), hu⟩ =
          QuotientGroup.mk (coreAct 8 (γ : Perm (Fin 8)) m) :=
    fun γ u m hu hm => hβeq γ u m hu (permAct_mem_coreMod _ m.2) hm
  refine ⟨π₀, hπs, hUinv, (QuotientGroup.quotientMulEquivOfEq altD8_ker).toMonoidHom.comp β₀,
    fun u => ?_, fun γ u => ?_⟩
  · rw [← hβk₀ u]
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  · obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β₀ u)
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [hβeq₀ γ u m _ hm.symm, ← hm, QuotientGroup.quotientMulEquivOfEq_mk,
      QuotientGroup.quotientMulEquivOfEq_mk, dAct_mk]

end S126M2

theorem factUv12618_of (h1222 : Stmt12_2_2) (h36 : QuasithinUnique.Vol2Native.A36ForSQTKCat)
    (h51 : AsB51) (hD7 : Lemma12_6_13) (hD9 : Lemma12_6_15) : FactUv12618 := by
  intro G _ _ T L V _ F v Kv S hC hKalt
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hH := hC.hyp
  have hv := hC.mem
  have hβ : F.β ⟨v, hv⟩ = QuotientGroup.mk (pe 0 1) := hC.coord
  have hyp := hH.hyp
  obtain ⟨⟨-, hO⟩, -, hVvU⟩ := hD7 G T L V F v Kv S hC
  set U := Usec Kv S with hU
  set X := Kv ⊔ S with hX
  have hUe := S126T2.isElemAbelian_Usec Kv S
  have : IsMulCommutative ↥U := hUe.1
  have hXU : X ≤ Subgroup.normalizer (U : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (S126T2.normalizer_le_normalizer_Usec Kv S)
  have hKvU : Kv ≤ Subgroup.normalizer (U : Set G) := S126T2.Kv_le_normalizer_Usec hC
  have hSK : S ≤ Subgroup.normalizer (Kv : Set G) := hC.sylow.1.trans hC.normal
  have hKS : X ≤ S126T2.Gv v := sup_le (le_of_mem_cComp hC.cComp) hC.sylow.1
  have hred := S126T2.isTwoReducedIn_Usec hD7 hC
  have hO2 : pCoreOf 2 (autOn X U) = ⊥ := QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hred
  have hH2 : pCoreOf 2 (S126T2.Gv v) ≠ ⊥ := S126T2.pCoreOf_Gv_ne_bot h1222 F hH hv hβ
  have hSQ : SQTKGroup ↥X := InternalSec.sqtkGroup_mono
    (sqtkGroup_of_pCoreOf_ne_bot hyp.qtke hyp.simple hyp.nonabelian hH2) hKS
  have hpow : ∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ Kv := by
    intro x hx
    have hx' : x ∈ (↑(Kv ⊔ S) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left Kv S hSK] at hx'
    obtain ⟨y, hy, t, ht, hyt⟩ := hx'
    obtain ⟨j, hj⟩ := hC.sylow.2.1 ⟨t, ht⟩
    have hj' : t ^ 2 ^ j = 1 := congrArg Subtype.val hj
    obtain ⟨y', hy', hp⟩ := A4.exists_pow_mul_eq hy (hSK ht) (2 ^ j)
    refine ⟨j, ?_⟩
    rw [← hyt, hp, hj', mul_one]
    exact hy'
  have hKs : IsSimpleGroup ↥(autOn Kv U) :=
    (MulEquiv.isSimpleGroup_congr (S126T2.autOn_Kv_equiv hD7 hC)).1
      (S126T2.isSimple_Kv h1222 h36 hC)
  obtain ⟨hU', hFF⟩ := hD9 G T L V F v Kv S hC
  set K := autOn Kv U with hKdef
  set A := autOn X U with hAdef
  set J := ffJ A with hJdef
  have hV2 : ∀ w : ↥U, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hUe.2 w w.2)
  have hJ1 : J ≠ ⊥ := InternalSec.ffJ_ne_bot_of_isFFModule hV2 hFF
  have hJA : J ≤ A := B6.ffJ_le A
  have hAJ : A ≤ Subgroup.normalizer (J : Set (MulAut ↥U)) := B6.le_normalizer_ffJ A
  have hKA : K ≤ A := InternalSec.autOn_le_autOn_of_le le_sup_left
  have hpowA : ∀ a ∈ A, ∃ k : ℕ, a ^ 2 ^ k ∈ K := by
    intro a ha
    obtain ⟨⟨x, hxN⟩, hxX, rfl⟩ := QuasithinUnique.Setup.mem_autOn_iff.1 ha
    obtain ⟨k, hk⟩ := hpow x hxX
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, by simpa using hk, rfl⟩
  have hKJ : K ≤ J := by
    rcases KG12614.le_or_inf_eq_bot hKs (hKA.trans hAJ) with h | h
    · exact h
    · exfalso
      apply hJ1
      have h2 : IsPGroup 2 ↥J := by
        rintro ⟨j, hj⟩
        obtain ⟨k, hk⟩ := hpowA j (hJA hj)
        have hk1 : j ^ 2 ^ k ∈ K ⊓ J := ⟨hk, J.pow_mem hj _⟩
        rw [h, Subgroup.mem_bot] at hk1
        exact ⟨k, Subtype.ext (by simpa using hk1)⟩
      have hle := le_pCoreOf_of_le_normalizer 2 hJA hAJ h2
      rw [hO2] at hle
      exact le_bot_iff.1 hle
  have hcardK : Nat.card ↥K = 2520 ∨ Nat.card ↥K = 20160 := by
    rcases hKalt with h | h
    · obtain ⟨e⟩ := h
      left
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      rfl
    · obtain ⟨e⟩ := h
      right
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      rfl
  have hnab : ∃ a b : ↥K, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥K := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := Group.is_simple_iff_prime_card.1 hKs
    rcases hcardK with h | h <;> rw [h] at hp <;> norm_num at hp
  have hq : CFSG.IsQuasisimple ↥K := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1
  have hSK' : SQTKGroup ↥K := G64.sqtkGroup_of_isSQTKCat (S126T2.isSQTKCat_autOn_Kv h1222 hD7 hC)
  have h2 : ∀ y ∈ X, ∃ e : ℕ, y ^ 2 ^ e ∈ Kv ⊔ Subgroup.centralizer (U : Set G) :=
    fun y hy => (hpow y hy).imp fun _ he => Subgroup.mem_sup_left he
  have hB : B51Hyp J K := LRed4.b51Hyp_of_K_le hXU le_sup_left (sup_le Subgroup.le_normalizer hSK)
    h2 hO2 hq hSK' hKJ
  obtain ⟨-, hP2, -, -, -, -⟩ := h51 ↥U hV2 J K hB
  have hcard2 := card_Vv_inf h1222 hH hv hβ
  obtain ⟨v₀, hv₀, hv₀1⟩ : ∃ v₀ ∈ Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G), v₀ ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) = ⊥ :=
      (Subgroup.eq_bot_iff_forall _).2 hall
    rw [h1, Subgroup.card_bot] at hcard2
    exact absurd hcard2 (by norm_num)
  refine ⟨v₀, hv₀, fun hv₀K => ?_⟩
  have hUKv : ⁅U, Kv⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have h1 : k * u⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.1 (hKvU hk) u⁻¹).1 (U.inv_mem hu)
    have h2 : ⁅u, k⁆ = u * (k * u⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
    rw [h2]
    exact U.mul_mem hu h1
  have hv₀U : v₀ ∈ U := hUKv (hVvU hv₀.1)
  set u₀ : ↥U := ⟨v₀, hv₀U⟩ with hu₀
  have hu₀1 : u₀ ≠ 1 := fun h => hv₀1 (congrArg Subtype.val h)
  have hu₀F : u₀ ∈ fixV K := by
    rw [fixV_autOn_eq hKvU, Subgroup.mem_subgroupOf]
    exact hv₀K
  have hu₀C : u₀ ∈ commV K := by
    have h1 : v₀ ∈ (commV K).map U.subtype := by
      rw [Vol2.Ch11.SecC.B51.map_commV_autOn hKvU]
      exact hVvU hv₀.1
    obtain ⟨u, hu, hue⟩ := h1
    rwa [show u = u₀ from Subtype.ext hue] at hu
  by_cases hdir : IsIntDirect (commV K) (fixV K) ⊤
  · have : u₀ ∈ commV K ⊓ fixV K := ⟨hu₀C, hu₀F⟩
    rw [hdir.2, Subgroup.mem_bot] at this
    exact hu₀1 this
  rcases hcardK with hc | hc
  · exact hdir (Vol2.Ch10.SecB.C11AmS.K8.part2_direct hP2 hc)
  obtain ⟨-, hlist⟩ := hP2.2 hdir
  have hN' : Nat.card ↥K = 20160 ∨ Nat.card ↥K = 9999360 := Or.inl hc
  have hnat : AlternatingNatural K (commV K) (fixV K ⊓ commV K) 8 := by
    rcases hlist with ⟨n, h⟩ | ⟨n, h⟩ | ⟨n, h⟩ | h | h | h | h
    · exact (not_binaryNaturalSL_two1527d hN' h).elim
    · exact (not_binaryNaturalSp4_1527d hN' h).elim
    · exact (not_g2Natural1527d hN' h).elim
    · exact (not_alternatingNatural1527d (n := 6) (by norm_num)
        (by rw [hc]; norm_num [Nat.factorial]) h).elim
    · exact h
    · exact (not_g2NaturalDerived_one1527d hN' h).elim
    · exact (not_binaryNaturalSL_three1527d hN' h).elim
  obtain ⟨π, hπs, hUinv, β', hβ'k, hβd⟩ := S126M2.exists_D8_of_alternatingNatural hnat
  have hA8 : IsSimpleGroup ↥(alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  have hπi : Function.Injective π := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal π.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff π).1 h
    · exfalso
      obtain ⟨a, ha⟩ := exists_ne (1 : ↥K)
      obtain ⟨γ, rfl⟩ := hπs a
      exact ha (π.mem_ker.1 (h ▸ Subgroup.mem_top γ))
  let πe : ↥(alternatingGroup (Fin 8)) ≃* ↥K := MulEquiv.ofBijective π ⟨hπi, hπs⟩
  have hLvU : Lv L v ≤ Subgroup.normalizer (U : Set G) := hC.lv_le.trans hKvU
  have hLvK : autOn (Lv L v) U ≤ K := InternalSec.autOn_le_autOn_of_le hC.lv_le
  let gK : ↥(Lv L v) →* ↥K := (Subgroup.inclusion hLvK).comp (InternalSec.autOnHom hLvU)
  have hgK : ∀ (l : ↥(Lv L v)) (u : ↥U),
      ((((gK l : ↥K) : MulAut ↥U) u : ↥U) : G) = (l : G) * u * (l : G)⁻¹ :=
    fun l u => QuasithinUnique.Setup.rho_apply_coe hLvU l u
  let ψ : ↥(Lv L v) →* Perm (Fin 8) :=
    (alternatingGroup (Fin 8)).subtype.comp (πe.symm.toMonoidHom.comp gK)
  have hψk : IsPGroup 2 ↥ψ.ker := by
    intro x
    have hx1 : gK (x : ↥(Lv L v)) = 1 := by
      have h1 : ψ x = 1 := MonoidHom.mem_ker.1 x.2
      have h2 : πe.symm (gK x) = 1 := by
        apply Subtype.ext
        simpa [ψ] using h1
      simpa using congrArg πe h2
    have hxC : ((x : ↥(Lv L v)) : G) ∈ Subgroup.centralizer (U : Set G) := by
      rw [← InternalSec.mem_ker_autOnHom hLvU, MonoidHom.mem_ker]
      have h2 : ((gK x : ↥K) : MulAut ↥U) = 1 := congrArg Subtype.val hx1
      exact Subtype.ext h2
    have hxO : ((x : ↥(Lv L v)) : G) ∈ pCoreOf 2 (Kv ⊔ S) := by
      rw [hO]
      exact ⟨(le_sup_left : Kv ≤ Kv ⊔ S) (hC.lv_le (x : ↥(Lv L v)).2), hxC⟩
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (Kv ⊔ S) ⟨_, hxO⟩
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  obtain ⟨f, hf, hfk, -⟩ := exists_psiLv h1222 F hH hv hβ
  have hB : ⁅(⊤ : Subgroup ↥(Lv L v)), (⊤ : Subgroup ↥(Lv L v))⁆ = ⊤ := by
    apply Subgroup.map_injective (Lv L v).subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact perfectCore_perfect _
  obtain ⟨τ, -, hψr⟩ := eq_conj_A6s_of_hom hB ψ hψk f hf hfk
  have hconj : ∀ σ ∈ A6s, ∃ l : ↥(Lv L v), ∃ hγ : τ * σ * τ⁻¹ ∈ alternatingGroup (Fin 8),
      gK l = π ⟨τ * σ * τ⁻¹, hγ⟩ := by
    intro σ hσ
    have hmem : τ * σ * τ⁻¹ ∈ ψ.range := by
      rw [hψr]
      exact ⟨σ, hσ, rfl⟩
    obtain ⟨l, hl⟩ := hmem
    have hγ : τ * σ * τ⁻¹ ∈ alternatingGroup (Fin 8) := by
      rw [← hl]
      exact (πe.symm (gK l)).2
    refine ⟨l, hγ, ?_⟩
    have h1 : πe.symm (gK l) = ⟨τ * σ * τ⁻¹, hγ⟩ := Subtype.ext hl
    rw [← h1]
    exact (πe.apply_symm_apply (gK l)).symm
  set ι : ↥(commV K) →* G := U.subtype.comp (commV K).subtype with hι
  have hιi : Function.Injective ι := U.subtype_injective.comp (commV K).subtype_injective
  set Wc := (Vv L V v).comap ι with hWc
  let β'' : ↥(commV K) →* D8 := (dAct τ⁻¹).comp β'
  have hβ''k : ∀ y : ↥(commV K), β'' y = 1 ↔ (y : ↥U) ∈ fixV K ⊓ commV K := by
    intro y
    rw [← hβ'k]
    constructor
    · intro h
      have h1 := congrArg (dAct τ) h
      rwa [map_one, show dAct τ (β'' y) = β' y from dAct_dAct_inv τ (β' y)] at h1
    · intro h
      show dAct τ⁻¹ (β' y) = 1
      rw [h, map_one]
  have hβ''d : ∀ σ ∈ A6s, ∀ u ∈ Wc, ∃ u' ∈ Wc, β'' u' = dAct σ (β'' u) := by
    intro σ hσ u hu
    obtain ⟨l, hγ, hl⟩ := hconj σ hσ
    refine ⟨⟨((π ⟨τ * σ * τ⁻¹, hγ⟩ : ↥K) : MulAut ↥U) (u : ↥U), hUinv _ u u.2⟩, ?_, ?_⟩
    · show ((((π ⟨τ * σ * τ⁻¹, hγ⟩ : ↥K) : MulAut ↥U) (u : ↥U) : ↥U) : G) ∈ Vv L V v
      rw [← hl, hgK]
      exact (Subgroup.mem_normalizer_iff.1 (Lv_le_normalizer_Vv hH v l.2) _).1 hu
    · show dAct τ⁻¹ (β' _) = dAct σ (dAct τ⁻¹ (β' u))
      have e : τ⁻¹ * ((⟨τ * σ * τ⁻¹, hγ⟩ : ↥(alternatingGroup (Fin 8))) : Perm (Fin 8)) =
          σ * τ⁻¹ := by
        show τ⁻¹ * (τ * σ * τ⁻¹) = σ * τ⁻¹
        group
      rw [hβd ⟨τ * σ * τ⁻¹, hγ⟩ u, ← dAct_mul, ← dAct_mul, e]
  have hWc32 : Nat.card Wc = 32 := by
    have h1 : Wc.map ι = Vv L V v := by
      apply le_antisymm (Subgroup.map_comap_le _ _)
      intro x hx
      have h2 : x ∈ (commV K).map U.subtype := by
        rw [Vol2.Ch11.SecC.B51.map_commV_autOn hKvU]
        exact hVvU hx
      obtain ⟨u, hu, rfl⟩ := h2
      exact ⟨⟨u, hu⟩, hx, rfl⟩
    rw [← card_Vv h1222 hH hv hβ, ← h1, Subgroup.card_map_of_injective hιi]
  set fW := β''.subgroupMap Wc with hfW
  have hfWk : ∀ x : ↥Wc, x ∈ fW.ker ↔ ((x : ↥(commV K)) : ↥U) ∈ fixV K ⊓ commV K := by
    intro x
    rw [MonoidHom.mem_ker, ← hβ''k]
    exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
  have hker2 : Nat.card fW.ker = 2 := by
    apply le_antisymm
    · have hmap : ∀ x : ↥fW.ker, ι ((x : ↥Wc) : ↥(commV K)) ∈
          Vv L V v ⊓ Subgroup.centralizer (Lv L v : Set G) := by
        intro x
        refine Subgroup.mem_inf.2 ⟨(x : ↥Wc).2, ?_⟩
        have h1 := (Subgroup.mem_inf.1 ((hfWk _).1 x.2)).1
        rw [fixV_autOn_eq hKvU, Subgroup.mem_subgroupOf] at h1
        exact Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hC.lv_le) h1
      refine le_of_le_of_eq (Nat.card_le_card_of_injective (fun x => ⟨_, hmap x⟩) ?_)
        (card_Vv_inf h1222 hH hv hβ)
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      apply hιi
      simpa using congrArg Subtype.val h
    · have hmem : (⟨⟨u₀, hu₀C⟩, hv₀.1⟩ : ↥Wc) ∈ fW.ker := (hfWk _).2 ⟨hu₀F, hu₀C⟩
      have hne : fW.ker ≠ ⊥ := by
        intro h
        rw [h, Subgroup.mem_bot] at hmem
        exact hu₀1 (congrArg Subtype.val (congrArg Subtype.val hmem))
      exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hW16 : Nat.card ↥(Wc.map β'') = 16 := by
    have h1 : Nat.card Wc = Nat.card ↥(Wc.map β'') * Nat.card fW.ker := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup fW.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective fW
          (β''.subgroupMap_surjective Wc)).toEquiv]
    rw [hWc32, hker2] at h1
    omega
  have : (Wc.map β'').Normal :=
    ⟨fun n hn g => by rw [S126L20a.D8_comm g n, mul_inv_cancel_right]; exact hn⟩
  have hpe : ∀ k : Fin 5,
      (QuotientGroup.mk (pe 2 (![3, 4, 5, 6, 7] k)) : D8) ∈ Wc.map β'' := by
    intro k
    have hσ := S126M2.s5_mem k
    have h := S126M2.mul_inv_mem_of_five (Wc.map β'') (dAct (S126M2.s5 k))
      (fun w hw => by
        obtain ⟨u, hu, rfl⟩ := hw
        obtain ⟨u', hu', he⟩ := hβ''d _ hσ u hu
        exact ⟨u', hu', he⟩)
      (fun d => by
        have h1 := dAct_pow (S126M2.s5 k) 5 d
        rw [S126M2.s5_pow k, dAct_one] at h1
        exact h1.symm)
      (by rw [S126L20.card_D8_eq, hW16]) (QuotientGroup.mk (pe 2 0))
    rwa [dAct_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      S126L20a.pe_mul_inv_coreAct _ 2 0 (S126M2.s5_zero k), S126M2.s5_two k] at h
  have h32 := S126M2.le_card_of_pe_mem (Wc.map β'') hpe
  omega

end CFSG.Quasithin.H13

end
