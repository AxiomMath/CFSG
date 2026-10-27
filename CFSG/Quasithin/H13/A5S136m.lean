module

public import CFSG.Quasithin.H13.A5S136l
public import CFSG.Quasithin.H13.A5S136i
public import CFSG.Quasithin.H13.A5S136c

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Quasithin CFSG.Quasithin.A5Model
open scoped commutatorElement

@[expose] def FactOutAlt67 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Subgroup G), CFSG.IsQuasisimple ↥K →
    (Nat.card (Subgroup.center ↥K) = 1 ∨ Nat.card (Subgroup.center ↥K) = 3) →
    (Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) ∨
      Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 7))) →
    ∀ g : G, g ∈ Subgroup.normalizer (K : Set G) → Odd (orderOf g) → InducesInner g K

@[expose] def cycThree {n : ℕ} (a b c : Fin n) : Equiv.Perm (Fin n) :=
  Equiv.swap a b * Equiv.swap b c

theorem centralizer_alt6 : ∀ τ : Equiv.Perm (Fin 6),
    τ * cycThree 0 1 2 = cycThree 0 1 2 * τ → τ * cycThree 3 4 5 = cycThree 3 4 5 * τ →
      τ * cycThree 1 2 3 = cycThree 1 2 3 * τ → τ = 1 := by
  decide +kernel

theorem perm_comm_apply {n : ℕ} {τ c : Equiv.Perm (Fin n)} (h : τ * c = c * τ) (p : Fin n) :
    τ (c p) = c (τ p) := by
  have := congrArg (fun f : Equiv.Perm (Fin n) => f p) h
  simpa [Equiv.Perm.mul_apply] using this

theorem perm_comm_supp {n : ℕ} {τ c : Equiv.Perm (Fin n)} (h : τ * c = c * τ) {p : Fin n}
    (hp : c p ≠ p) : c (τ p) ≠ τ p := by
  intro h'
  apply hp
  have h1 := perm_comm_apply h p
  rw [h'] at h1
  exact τ.injective h1

theorem centralizer_alt7 : ∀ τ : Equiv.Perm (Fin 7),
    τ * cycThree 0 1 2 = cycThree 0 1 2 * τ → τ * cycThree 2 3 4 = cycThree 2 3 4 * τ →
      τ * cycThree 4 5 6 = cycThree 4 5 6 * τ → τ = 1 := by
  intro τ h1 h2 h3
  have i2 : ∀ q : Fin 7, cycThree 0 1 2 q ≠ q → cycThree 2 3 4 q ≠ q → q = 2 := by decide
  have i4 : ∀ q : Fin 7, cycThree 2 3 4 q ≠ q → cycThree 4 5 6 q ≠ q → q = 4 := by decide
  have t2 : τ 2 = 2 :=
    i2 _ (perm_comm_supp h1 (by decide)) (perm_comm_supp h2 (by decide))
  have t4 : τ 4 = 4 :=
    i4 _ (perm_comm_supp h2 (by decide)) (perm_comm_supp h3 (by decide))
  have t0 : τ 0 = 0 := by
    have := perm_comm_apply h1 2
    rw [t2, show cycThree (0 : Fin 7) 1 2 2 = 0 by decide] at this
    exact this
  have t1 : τ 1 = 1 := by
    have := perm_comm_apply h1 0
    rw [t0, show cycThree (0 : Fin 7) 1 2 0 = 1 by decide] at this
    exact this
  have t3 : τ 3 = 3 := by
    have := perm_comm_apply h2 2
    rw [t2, show cycThree (2 : Fin 7) 3 4 2 = 3 by decide] at this
    exact this
  have t5 : τ 5 = 5 := by
    have := perm_comm_apply h3 4
    rw [t4, show cycThree (4 : Fin 7) 5 6 4 = 5 by decide] at this
    exact this
  have t6 : τ 6 = 6 := by
    have := perm_comm_apply h3 5
    rw [t5, show cycThree (4 : Fin 7) 5 6 5 = 6 by decide] at this
    exact this
  ext x
  fin_cases x <;> simp [t0, t1, t2, t3, t4, t5, t6]

theorem cycThree_sign {n : ℕ} (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) :
    (cycThree a b c).sign = 1 := by
  rw [cycThree, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab, Equiv.Perm.sign_swap hbc]
  decide

section Inner

variable {G : Type} [Group G]

theorem conj_eq_of_inner_of_permAction {n : ℕ} {K : Subgroup G} {z : G}
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin n)) {σ : Equiv.Perm (Fin n)}
    (hinner : InducesInner z K) (hact : InducesPermAction z K φ σ) :
    ∃ lam : alternatingGroup (Fin n), ∀ a : alternatingGroup (Fin n),
      σ⁻¹ * (a : Equiv.Perm (Fin n)) * σ =
        ((lam⁻¹ : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * a * lam := by
  obtain ⟨l, hlK, hl⟩ := hinner
  refine ⟨φ (QuotientGroup.mk (⟨l, hlK⟩ : ↥K)), fun a => ?_⟩
  obtain ⟨q, hq⟩ := φ.surjective a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  set y : ↥K := ⟨l⁻¹ * (x : G) * l, K.mul_mem (K.mul_mem (K.inv_mem hlK) x.2) hlK⟩ with hy
  have hyz : (y : G) = z⁻¹ * (x : G) * z := (hl x x.2).symm
  have h1 := hact.2 x y hyz
  have hyx : y = (⟨l, hlK⟩ : ↥K)⁻¹ * x * ⟨l, hlK⟩ := Subtype.ext rfl
  rw [hyx, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, map_mul, map_mul,
    map_inv, hq] at h1
  rw [← h1]
  simp

theorem false_of_inner_of_permAction6 {K : Subgroup G} {z : G}
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) {σ : Equiv.Perm (Fin 6)}
    (hσ : σ.sign ≠ 1) (hinner : InducesInner z K) (hact : InducesPermAction z K φ σ) : False := by
  obtain ⟨lam, hlam⟩ := conj_eq_of_inner_of_permAction φ hinner hact
  have key : ∀ a : alternatingGroup (Fin 6),
      (σ * ((lam⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) * a =
        a * (σ * ((lam⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6))) := by
    intro a
    have h := hlam a
    have e1 : σ * ((lam⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * a =
        σ * (((lam⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) * a * lam) *
          ((lam⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) := by
      simp [mul_assoc]
    rw [e1, ← h]
    simp [mul_assoc]
  have ha : ∀ (a b c : Fin 6), a ≠ b → b ≠ c → cycThree a b c ∈ alternatingGroup (Fin 6) :=
    fun a b c hab hbc => Equiv.Perm.mem_alternatingGroup.mpr (cycThree_sign a b c hab hbc)
  have hτ := centralizer_alt6 _ (key ⟨_, ha 0 1 2 (by decide) (by decide)⟩)
    (key ⟨_, ha 3 4 5 (by decide) (by decide)⟩) (key ⟨_, ha 1 2 3 (by decide) (by decide)⟩)
  have hsl : σ = (lam : Equiv.Perm (Fin 6)) := by
    have := congrArg (· * (lam : Equiv.Perm (Fin 6))) hτ
    simpa [mul_assoc] using this
  apply hσ
  rw [hsl]
  exact Equiv.Perm.mem_alternatingGroup.mp lam.2

theorem false_of_inner_of_permAction7 {K : Subgroup G} {z : G}
    (φ : (↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 7)) {σ : Equiv.Perm (Fin 7)}
    (hσ : σ.sign ≠ 1) (hinner : InducesInner z K) (hact : InducesPermAction z K φ σ) : False := by
  obtain ⟨lam, hlam⟩ := conj_eq_of_inner_of_permAction φ hinner hact
  have key : ∀ a : alternatingGroup (Fin 7),
      (σ * ((lam⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) * a =
        a * (σ * ((lam⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7))) := by
    intro a
    have h := hlam a
    have e1 : σ * ((lam⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * a =
        σ * (((lam⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) * a * lam) *
          ((lam⁻¹ : alternatingGroup (Fin 7)) : Equiv.Perm (Fin 7)) := by
      simp [mul_assoc]
    rw [e1, ← h]
    simp [mul_assoc]
  have ha : ∀ (a b c : Fin 7), a ≠ b → b ≠ c → cycThree a b c ∈ alternatingGroup (Fin 7) :=
    fun a b c hab hbc => Equiv.Perm.mem_alternatingGroup.mpr (cycThree_sign a b c hab hbc)
  have hτ := centralizer_alt7 _ (key ⟨_, ha 0 1 2 (by decide) (by decide)⟩)
    (key ⟨_, ha 2 3 4 (by decide) (by decide)⟩) (key ⟨_, ha 4 5 6 (by decide) (by decide)⟩)
  have hsl : σ = (lam : Equiv.Perm (Fin 7)) := by
    have := congrArg (· * (lam : Equiv.Perm (Fin 7))) hτ
    simpa [mul_assoc] using this
  apply hσ
  rw [hsl]
  exact Equiv.Perm.mem_alternatingGroup.mp lam.2

theorem InducesInner.mul {K : Subgroup G} {g h : G} (hg : InducesInner g K)
    (hh : InducesInner h K) : InducesInner (g * h) K := by
  obtain ⟨l, hl, hgl⟩ := hg
  obtain ⟨l', hl', hhl⟩ := hh
  refine ⟨l * l', K.mul_mem hl hl', fun x hx => ?_⟩
  have h1 : (g * h)⁻¹ * x * (g * h) = h⁻¹ * (g⁻¹ * x * g) * h := by group
  rw [h1, hgl x hx]
  have h2 : l⁻¹ * x * l ∈ K := K.mul_mem (K.mul_mem (K.inv_mem hl) hx) hl
  rw [hhl _ h2]
  group

theorem InducesInner.inv {K : Subgroup G} {g : G} (hg : InducesInner g K)
    (hgN : g ∈ Subgroup.normalizer (K : Set G)) : InducesInner g⁻¹ K := by
  obtain ⟨l, hl, hgl⟩ := hg
  refine ⟨l⁻¹, K.inv_mem hl, fun x hx => ?_⟩
  have hx' : g * x * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hgN x).mp hx
  have h1 := hgl _ hx'
  have e : g⁻¹ * (g * x * g⁻¹) * g = x := by group
  rw [e] at h1
  simp only [inv_inv]
  calc g * x * g⁻¹ = l * (l⁻¹ * (g * x * g⁻¹) * l) * l⁻¹ := by group
    _ = l * x * l⁻¹ := by rw [← h1]

end Inner

theorem mem_of_index_two_of_odd {X : Type} [Group X] {H : Subgroup X} (h : H.index = 2) {g : X}
    {m : ℕ} (hm : Odd m) (hg : g ^ m = 1) : g ∈ H := by
  obtain ⟨k, rfl⟩ := hm
  have hsq : g ^ 2 ∈ H := by
    rw [pow_two]
    exact Subgroup.mul_self_mem_of_index_two h g
  have hk : (g ^ 2) ^ k ∈ H := H.pow_mem hsq k
  have e : g ^ (2 * k + 1) = (g ^ 2) ^ k * g := by rw [pow_succ, pow_mul]
  rw [e] at hg
  have := (Subgroup.mul_mem_iff_of_index_two h).mp (hg ▸ H.one_mem)
  exact this.mp hk

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem V_le_normalizer_Lv : V ≤ Subgroup.normalizer (S.Lv : Set G) := by
  have hVGv : V ≤ Subgroup.centralizer ({S.v12} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (S.elemAbelian_V.1.is_comm.comm ⟨u, hu⟩ ⟨S.v12, S.v12_mem_V⟩))
  refine le_normalizer_oTwoRes fun u hu => ?_
  have huL : u ∈ Subgroup.normalizer (L : Set G) := S.T_le_NL (S.V_le_T hu)
  have huG : u ∈ Subgroup.centralizer ({S.v12} : Set G) := hVGv hu
  set Gv := Subgroup.centralizer ({S.v12} : Set G)
  refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
  · exact ⟨(Subgroup.mem_normalizer_iff.mp huL x).mp hx.1,
      Gv.mul_mem (Gv.mul_mem huG hx.2) (Gv.inv_mem huG)⟩
  · refine ⟨?_, Gv.mul_mem (Gv.mul_mem (Gv.inv_mem huG) hx.2) huG⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huL) x).mp hx.1
    simpa using this

theorem commutator_V_Lv_le : ⁅V, S.Lv⁆ ≤ S.Lv := by
  rw [Subgroup.commutator_le]
  intro u hu l hl
  rw [commutatorElement_def]
  have h1 : u * l * u⁻¹ ∈ S.Lv := (Subgroup.mem_normalizer_iff.mp (S.V_le_normalizer_Lv hu) l).mp hl
  exact S.Lv.mul_mem h1 (S.Lv.inv_mem hl)

theorem z_mul_inv_v12_mem_Lv : S.z * S.v12⁻¹ ∈ S.Lv := by
  refine S.commutator_V_Lv_le ?_
  rw [S.commutator_V_Lv.1]
  refine S.mem_pre.2 ⟨V.mul_mem S.z_mem_V (V.inv_mem S.v12_mem_V), ?_⟩
  have e : (⟨S.z * S.v12⁻¹, V.mul_mem S.z_mem_V (V.inv_mem S.v12_mem_V)⟩ : ↥V) =
      ⟨S.z, S.z_mem_V⟩ * (⟨S.v12, S.v12_mem_V⟩)⁻¹ := rfl
  rw [e, map_mul, map_inv, S.psi_z, S.psi_v12]
  exact W4_E12_mem

theorem Lv_le_normalizer_of_mem_cComp (h1222 : Stmt12_2_2)
    (h517 : Stmt5_1_7_one) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {K : Subgroup G} (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G))) :
    S.Lv ≤ Subgroup.normalizer (K : Set G) := by
  have : IsSimpleGroup G := S.h13.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat S.h13.nonabelian S.h13.qtke).1
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hO2 := (S.lemma115Hyp_Gv h1222 h517).pCore_ne_bot
  have hKG : K ≤ Gv := le_of_mem_cComp hK
  have hLvGv : S.Lv ≤ Gv := by
    rw [Lv, oTwoRes_eq_oTwoUpper]
    exact (oTwoUpper_le _).trans inf_le_right
  rcases Vol2Native.lemma_1_2_1_three hloc h37 h38 hO2 hK with hn | ⟨h2, -⟩
  · exact hLvGv.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKG).mp hn)
  · rw [ncard_conjSubgroupsBy_eq_index] at h2
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, m, hm, hxm⟩
    have hxG : x ∈ Gv := hx.2
    have h1 : (⟨x, hxG⟩ : ↥Gv) ∈ (Subgroup.normalizer (K : Set G)).subgroupOf Gv :=
      mem_of_index_two_of_odd h2 hm (Subtype.ext (by simpa using hxm))
    exact Subgroup.mem_subgroupOf.mp h1

end Setting

theorem elim1366CD_of (h1222 : Stmt12_2_2) (h517 : Stmt5_1_7_one)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (hout : FactOutAlt67) :
    Elim1366CD := by
  intro G _ _ T L V S hab K hK hcase
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hLvN := S.Lv_le_normalizer_of_mem_cComp h1222 h517 h37 h38 hKc
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have hinner : (Nat.card (Subgroup.center ↥K) = 1 ∨ Nat.card (Subgroup.center ↥K) = 3) →
      (Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 6)) ∨
        Nonempty ((↥K ⧸ Subgroup.center ↥K) ≃* alternatingGroup (Fin 7))) →
      InducesInner S.z K := by
    intro hZ hshape
    have hLv : ∀ x ∈ S.Lv, InducesInner x K := by
      intro x hx
      have hx' : x ∈ Subgroup.closure
          {y | y ∈ L ⊓ Gv ∧ ∃ m : ℕ, Odd m ∧ y ^ m = 1} := hx
      clear hx
      induction hx' using Subgroup.closure_induction with
      | mem y hy =>
        obtain ⟨hy1, m, hm, hym⟩ := hy
        exact hout G K hqs hZ hshape y (hLvN (Subgroup.subset_closure ⟨hy1, m, hm, hym⟩))
          (Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hym))
      | one => exact ⟨1, K.one_mem, fun x _ => by group⟩
      | mul a b ha hb iha ihb => exact InducesInner.mul iha ihb
      | inv a ha iha => exact InducesInner.inv iha (hLvN ha)
    obtain ⟨l, hl, hwl⟩ := hLv _ S.z_mul_inv_v12_mem_Lv
    refine ⟨l, hl, fun x hx => ?_⟩
    have hxv : x * S.v12 = S.v12 * x := Subgroup.mem_centralizer_singleton_iff.mp (hKG hx)
    have h1 := hwl x hx
    have h2 : (S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹) ∈ K := by
      rw [h1]
      exact K.mul_mem (K.mul_mem (K.inv_mem hl) hx) hl
    have hv2 : (S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹) * S.v12 =
        S.v12 * ((S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹)) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKG h2)
    rw [← h1]
    calc S.z⁻¹ * x * S.z = S.v12⁻¹ * ((S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹)) * S.v12 := by
          group
      _ = S.v12⁻¹ * (S.v12 * ((S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹))) := by
          rw [mul_assoc, hv2]
      _ = (S.z * S.v12⁻¹)⁻¹ * x * (S.z * S.v12⁻¹) := by group
  rcases hcase with ⟨φ, σ, hZ, hswap, hact⟩ | ⟨φ, σ, hZ, hcyc, hact⟩
  · refine false_of_inner_of_permAction6 φ ?_ (hinner hZ (Or.inl ⟨φ⟩)) hact
    rw [hswap.sign_eq]
    decide
  · refine false_of_inner_of_permAction7 φ ?_ (hinner hZ (Or.inr ⟨φ⟩)) hact
    rw [Equiv.Perm.sign_of_cycleType, hcyc]
    decide

end CFSG.Quasithin.H13.A5
