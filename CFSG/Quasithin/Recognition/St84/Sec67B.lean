module

public import CFSG.Quasithin.Recognition.St84.Sec67A
public import CFSG.Quasithin.Recognition.St84.Sec6A5Module
public import CFSG.Quasithin.Recognition.St84.Gen.L2SecDim
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
public import CFSG.Quasithin.Recognition.GoldschmidtFan86B2Layers
import CFSG.Quasithin.Recognition.St84.Gen.DicksonTrans
public import CFSG.LieType.SteinbergBROddSylowCore

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86
open CFSG.QuasithinUnique.Setup.Campbell
open CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

namespace Setup

variable (X : Setup Γ G)

private theorem Gi_neg_one_le_normalizer_VnegOne :
    X.Gi (-1) ≤ Subgroup.normalizer (X.VnegOne : Set G) := by
  intro g hg
  have hstep : ∀ g' ∈ X.Gi (-1), conjSub g' X.VnegOne ≤ X.VnegOne := by
    intro g' hg'
    change conjSub g' (⨆ (h : G), ⨆ (_ : h ∈ X.Gi (-1)), conjSub h (X.Z 0)) ≤ X.VnegOne
    rw [conjSub_iSup]
    refine iSup_le fun h => ?_
    rw [conjSub_iSup]
    refine iSup_le fun hh => ?_
    rw [← conjSub_mul]
    exact le_iSup₂_of_le (g' * h) ((X.Gi (-1)).mul_mem hg' hh) le_rfl
  have h1 := hstep g hg
  have h2 := hstep g⁻¹ ((X.Gi (-1)).inv_mem hg)
  have h3 : X.VnegOne ≤ conjSub g X.VnegOne := by
    have := conjSub_mono g h2
    rwa [conjSub_inv_conjSub] at this
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (le_antisymm h1 h3)

private theorem conjSub_tau_VnegOne_le_Vone : conjSub X.τ X.VnegOne ≤ X.Vone := by
  unfold Setup.VnegOne
  rw [conjSub_iSup]
  refine iSup_le fun g => ?_
  rw [conjSub_iSup]
  refine iSup_le fun hg => ?_
  have hG1 : X.τ * g * X.τ⁻¹ ∈ X.Gi 1 := by
    have hGi : X.Gi 1 = conjSub X.τ (X.Gi (-1)) := by
      simpa using X.Gi_add 1 (-1)
    rw [hGi, mem_conjSub]
    have hconj : X.τ⁻¹ * (X.τ * g * X.τ⁻¹) * X.τ = g := by group
    simpa [hconj] using hg
  have hτZ : conjSub X.τ (X.Z 0) = X.Z 2 :=
    X.Z_conj (by simpa using X.zpow_smul_vert 1 0)
  have hsplit : X.τ * g = (X.τ * g * X.τ⁻¹) * X.τ := by group
  rw [show conjSub X.τ (conjSub g (X.Z 0)) = conjSub (X.τ * g) (X.Z 0) from
    (conjSub_mul X.τ g (X.Z 0)).symm, hsplit, conjSub_mul, hτZ]
  obtain ⟨h2, hh2, h2v⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).trans (X.vert 0)
    (X.vert 2) (X.adj 0).symm (X.adj 1)
  have hZ2eq : X.Z 2 = conjSub h2 (X.Z 0) := (X.Z_conj h2v).symm
  rw [hZ2eq, ← conjSub_mul]
  exact le_iSup₂_of_le _ (Subgroup.mul_mem _ hG1 (oTwoPrime_le (X.Gi 1) hh2)) le_rfl

private theorem conjSub_tau_VnegOne_le_Q_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    conjSub X.τ X.VnegOne ≤ X.Q 1 :=
  (conjSub_tau_VnegOne_le_Vone X).trans
    (X.Vone_le_Q_one hGT hs hodd h5 hX)

theorem Ki_zero_eq_bot (hn0 : X.n 0 = 1) : X.Ki 0 = ⊥ := by
  have hcard : Nat.card ↥(X.Ki 0) = 1 := by
    rw [X.card_Ki 0, hn0]
    norm_num
  exact (Subgroup.eq_bot_iff_card (X.Ki 0)).mpr hcard

theorem K_eq_Ki_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) : X.K = X.Ki 1 := by
  have h := X.K_eq_sup_edge 0
  rw [Ki_zero_eq_bot X hn0, bot_sup_eq] at h
  exact h

theorem Gi_one_eq_L_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) : X.Gi 1 = X.L 1 := by
  have hfr := frattini_oTwoPrime X.hyp (X.adj 0).symm
  have hK : X.K ≤ X.L 1 :=
    (K_eq_Ki_one X hb hc hGT hs hodd h5 hX hn0).le.trans inf_le_right
  have hS : X.S ≤ X.L 1 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hle : X.Gi 1 ⊓ X.Gi 0 ≤ X.L 1 := by
    have h := X.K_sup_edgeSylow 0
    rw [X.edgeSylow_zero] at h
    change X.K ⊔ X.S = X.Gi 0 ⊓ X.Gi 1 at h
    rw [inf_comm (X.Gi 1) (X.Gi 0), ← h]
    exact sup_le hK hS
  change (X.Gi 1 ⊓ X.Gi 0) ⊔ X.L 1 = X.Gi 1 at hfr
  rw [sup_eq_right.mpr hle] at hfr
  exact hfr.symm

private theorem card_conj_le_two {A : Subgroup G} {q' q : G} (g : G)
    (hq : q = g * q' * g⁻¹)
    (h : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer ({q'} : Set G))) :
    Nat.card (conjSub g A) ≤
      2 * Nat.card ↥(conjSub g A ⊓ Subgroup.centralizer ({q} : Set G)) := by
  have hinf : conjSub g A ⊓ Subgroup.centralizer ({q} : Set G) =
      conjSub g (A ⊓ Subgroup.centralizer ({q'} : Set G)) := by
    rw [hq, conjSub, conjSub, CFSG.centralizer_inter_map, MulAut.conj_apply]
  rw [hinf, CFSG.Quasithin.St84.card_conjSub, CFSG.Quasithin.St84.card_conjSub]
  exact h

private theorem card_le_two_of_commutator {A : Subgroup G} {q : G} [Finite ↥A]
    (hZ : Nat.card ↥(X.Z 1) ≤ 2)
    (hcomm : ∀ a ∈ A, ⁅a, q⁆ ∈ X.Z 1) :
    Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) := by
  haveI : Finite ↥(X.Z 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 1)
      ((X.Z_le_Q 1).trans (X.Q_le_Gi 1))
  letI : MulAction ↥A G :=
    MulAction.compHom G (ConjAct.toConjAct.toMonoidHom.comp A.subtype)
  have hmemZ1 : ∀ a : ↥A, (a : G) * q * (a : G)⁻¹ * q⁻¹ ∈ X.Z 1 := by
    intro a
    simpa only [commutatorElement_def] using hcomm a a.2
  let f : MulAction.orbit ↥A q → ↥(X.Z 1) := fun u =>
    ⟨u.1 * q⁻¹, by
      obtain ⟨a, ha⟩ := u.2
      rw [← ha]
      change (a : G) * q * (a : G)⁻¹ * q⁻¹ ∈ X.Z 1
      exact hmemZ1 a⟩
  have hf : Function.Injective f := by
    intro u₁ u₂ h
    apply Subtype.ext
    have h' := congrArg Subtype.val h
    dsimp [f] at h'
    exact mul_right_cancel h'
  have horb : Nat.card (MulAction.orbit ↥A q) ≤ 2 := by
    have h := Nat.card_le_card_of_injective f hf
    exact le_trans h (by exact_mod_cast hZ)
  have hstab : MulAction.stabilizer ↥A q =
      (A ⊓ Subgroup.centralizer ({q} : Set G)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff]
    constructor
    · intro ha
      refine Subgroup.mem_subgroupOf.mpr ⟨a.2, ?_⟩
      change (a : G) ∈ Subgroup.centralizer ({q} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change (a : G) * q * (a : G)⁻¹ = q at ha
      calc (a : G) * q = ((a : G) * q * (a : G)⁻¹) * (a : G) := by group
        _ = q * (a : G) := by rw [ha]
    · intro ha
      obtain ⟨-, hc⟩ := Subgroup.mem_subgroupOf.mp ha
      change (a : G) ∈ Subgroup.centralizer ({q} : Set G) at hc
      rw [Subgroup.mem_centralizer_singleton_iff] at hc
      change (a : G) * q * (a : G)⁻¹ = q
      rw [hc]
      group
  have hidx : (A ⊓ Subgroup.centralizer ({q} : Set G)).relIndex A ≤ 2 := by
    rw [← Subgroup.relIndex_subgroupOf (le_rfl : A ≤ A)]
    have htop : A.subgroupOf A = ⊤ := by
      ext x
      simp
    rw [htop, Subgroup.relIndex_top_right, ← hstab, MulAction.index_stabilizer]
    exact horb
  have hcard : (A ⊓ Subgroup.centralizer ({q} : Set G)).relIndex A *
      Nat.card ↥(A ⊓ Subgroup.centralizer ({q} : Set G)) = Nat.card A := by
    have h := Subgroup.relIndex_mul_card
      (H := A ⊓ Subgroup.centralizer ({q} : Set G)) (K := A)
    simpa [inf_assoc, inf_left_comm, inf_comm] using h
  rw [← hcard]
  exact Nat.mul_le_mul_right _ hidx

private theorem K_le_normalizer_conj_Vone :
    X.K ≤ Subgroup.normalizer (conjSub X.τ X.Vone : Set G) :=
  (CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer X.τ_norm).symm.le.trans
    (CFSG.Quasithin.conjSub_le_normalizer
      ((X.K_le_Gi 1).trans (Gi_one_le_normalizer_Vone X)))

private theorem K_le_normalizer_conj_Q_zero :
    X.K ≤ Subgroup.normalizer (conjSub X.τ (X.Q 0) : Set G) :=
  (CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer X.τ_norm).symm.le.trans
    (CFSG.Quasithin.conjSub_le_normalizer
      ((X.K_le_Gi 0).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))))

private theorem K_le_normalizer_VnegOne_inf_Q_zero_sup :
    X.K ≤ Subgroup.normalizer
      (((X.VnegOne ⊓ X.Q 0) ⊔ conjSub X.τ (X.Vone ⊓ X.Q 0) : Subgroup G) : Set G) := by
  have hKB : X.K ≤ Subgroup.normalizer ((X.VnegOne ⊓ X.Q 0 : Subgroup G) : Set G) := by
    refine (le_inf ?_ ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := X.VnegOne) (K := X.Q 0))
    · exact (X.K_le_Gi (-1)).trans (Gi_neg_one_le_normalizer_VnegOne X)
    · exact (X.K_le_Gi 0).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hKAtau : X.K ≤ Subgroup.normalizer
      (conjSub X.τ (X.Vone ⊓ X.Q 0) : Set G) := by
    rw [conjSub_inf]
    refine (le_inf ?_ ?_).trans
      (Subgroup.inf_normalizer_le_normalizer_inf
        (H := conjSub X.τ X.Vone) (K := conjSub X.τ (X.Q 0)))
    · exact K_le_normalizer_conj_Vone X
    · exact K_le_normalizer_conj_Q_zero X
  exact CFSG.Quasithin.F1.le_normalizer_sup hKB hKAtau

private theorem le_normalizer_Z_of_le_Gi {H : Subgroup G} {i : ℤ} (h : H ≤ X.Gi i) :
    H ≤ Subgroup.normalizer (X.Z i : Set G) := fun g hg =>
  Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal i g (h hg))

private theorem L_eq_edgeSylow_sup_Q (i : ℤ) :
    X.L i = X.edgeSylow (i - 1) ⊔ X.edgeSylow i ⊔ X.Q i := by
  have h := X.L_eq_sup_of_fixes i (A := X.edgeSylow (i - 1)) (B := X.edgeSylow i)
    (a := X.vert (i - 1)) (b := X.vert (i + 1))
    (by simpa using (X.adj (i - 1)).symm) (X.adj i)
    (X.vert_injective.ne (by omega))
    (by simpa using (X.isSylowTwoOf_edgeSylow_L_succ (i - 1)).1)
    (X.isSylowTwoOf_edgeSylow_L i).1
    ((X.isSylowTwoOf_edgeSylow (i - 1)).1.trans inf_le_left)
    ((X.isSylowTwoOf_edgeSylow i).1.trans inf_le_right)
    (by
      rw [inf_eq_right.mpr (by simpa using X.Q_le_edgeSylow (i - 1))]
      simpa using X.relIndex_Q_succ_edgeSylow (i - 1))
    (by
      rw [inf_eq_right.mpr (X.Q_le_edgeSylow_left i)]
      exact X.relIndex_Q_edgeSylow i)
  exact h

private theorem Z_two_le_Vone : X.Z 2 ≤ X.Vone := by
  obtain ⟨h2, hh2, h2v⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).trans (X.vert 0)
    (X.vert 2) (X.adj 0).symm (X.adj 1)
  rw [← X.Z_conj h2v]
  exact le_iSup₂_of_le h2 (oTwoPrime_le (X.Gi 1) hh2) le_rfl

private theorem commutator_VnegOne_Q_neg_one_le (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.VnegOne, X.Q (-1)⁆ ≤ X.Z (-1) := by
  have hle : X.VnegOne ≤ conjSub X.τ⁻¹ X.Vone := by
    have h := conjSub_mono X.τ⁻¹
      (conjSub_tau_VnegOne_le_Vone X)
    rwa [conjSub_conjSub_inv] at h
  have hcomm := congrArg (conjSub X.τ⁻¹)
    (commutator_Vone_Q_one X hb hc hGT hs hodd h5 hX)
  rw [← conjSub_commutator] at hcomm
  have hQ : conjSub X.τ⁻¹ (X.Q 1) = X.Q (-1) := by
    simpa using (X.Q_add (-1) 1).symm
  have hZ : conjSub X.τ⁻¹ (X.Z 1) = X.Z (-1) := by
    simpa using (X.Z_add (-1) 1).symm
  rw [hQ, hZ] at hcomm
  calc ⁅X.VnegOne, X.Q (-1)⁆ ≤ ⁅conjSub X.τ⁻¹ X.Vone, X.Q (-1)⁆ :=
        Subgroup.commutator_mono hle le_rfl
    _ = X.Z (-1) := hcomm

private theorem commutator_QT_VnegOne_le_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.QT, X.VnegOne ⊓ X.Q 0⁆ ≤ X.Vone := by
  have hZneg : X.Z (-1) ≤ X.Z 0 :=
    le_sup_right.trans
      (Z_zero_eq_Z_one_sup_Z_neg_one X hb hc hGT hs hodd h5 hX).ge
  calc ⁅X.QT, X.VnegOne ⊓ X.Q 0⁆ ≤ ⁅X.Q (-1), X.VnegOne⁆ :=
        Subgroup.commutator_mono (X.QT_le_Q (-1)) inf_le_left
    _ = ⁅X.VnegOne, X.Q (-1)⁆ := Subgroup.commutator_comm ..
    _ ≤ X.Z (-1) := commutator_VnegOne_Q_neg_one_le X hb hc hGT hs hodd h5 hX
    _ ≤ X.Z 0 := hZneg
    _ ≤ X.Vone := Z_zero_le_Vone X

private theorem commutator_QT_conj_Vone_le_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.QT, conjSub X.τ (X.Vone ⊓ X.Q 0)⁆ ≤ X.Vone := by
  have hAtau : conjSub X.τ (X.Vone ⊓ X.Q 0) ≤ conjSub X.τ X.Vone :=
    conjSub_mono X.τ inf_le_left
  have hQ3 : X.QT ≤ X.Q 3 := X.QT_le_Q 3
  have hQ31 : conjSub X.τ (X.Q 1) = X.Q 3 := by
    simpa using (X.Q_add 1 1).symm
  have hZ3 : conjSub X.τ (X.Z 1) = X.Z 3 := by
    simpa using (X.Z_add 1 1).symm
  have hcomm := congrArg (conjSub X.τ)
    (commutator_Vone_Q_one X hb hc hGT hs hodd h5 hX)
  rw [← conjSub_commutator, hQ31, hZ3] at hcomm
  have hZ3V : X.Z 3 ≤ X.Vone := by
    have hZ32 : X.Z 3 ≤ X.Z 2 := by
      rw [← hZ3]
      calc conjSub X.τ (X.Z 1) ≤ conjSub X.τ (X.Z 0) := by
            refine conjSub_mono X.τ ?_
            have hZ0 := Z_zero_eq_Z_one_sup_Z_neg_one X hb hc hGT hs hodd h5 hX
            rw [hZ0]
            exact le_sup_left
        _ = X.Z 2 := by simpa using (X.Z_add 1 0).symm
    exact hZ32.trans (Z_two_le_Vone X)
  calc ⁅X.QT, conjSub X.τ (X.Vone ⊓ X.Q 0)⁆ ≤ ⁅X.Q 3, conjSub X.τ X.Vone⁆ :=
        Subgroup.commutator_mono hQ3 hAtau
    _ = ⁅conjSub X.τ X.Vone, X.Q 3⁆ := Subgroup.commutator_comm ..
    _ = X.Z 3 := hcomm
    _ ≤ X.Vone := hZ3V

private theorem commutator_QT_D_le_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) :
    ⁅X.QT, (X.VnegOne ⊓ X.Q 0) ⊔ conjSub X.τ (X.Vone ⊓ X.Q 0)⁆ ≤ X.Vone := by
  have hBnorm : X.VnegOne ⊓ X.Q 0 ≤ Subgroup.normalizer (X.Vone : Set G) := by
    refine (show X.VnegOne ⊓ X.Q 0 ≤ X.Gi 1 from ?_).trans
      (Gi_one_le_normalizer_Vone X)
    exact inf_le_right.trans (by simpa using (X.Q_le_Gi_adj 0).trans inf_le_right)
  have hAtauNorm : conjSub X.τ (X.Vone ⊓ X.Q 0) ≤
      Subgroup.normalizer (X.Vone : Set G) := by
    refine (show conjSub X.τ (X.Vone ⊓ X.Q 0) ≤ X.Gi 1 from ?_).trans
      (Gi_one_le_normalizer_Vone X)
    calc conjSub X.τ (X.Vone ⊓ X.Q 0) ≤ conjSub X.τ (X.Q 0) :=
          conjSub_mono X.τ inf_le_right
      _ = X.Q 2 := by simpa using (X.Q_add 1 0).symm
      _ ≤ X.Gi 1 := by simpa using (X.Q_le_Gi_adj 2).trans inf_le_left
  have h := CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
    (G := G) (X.VnegOne ⊓ X.Q 0) (conjSub X.τ (X.Vone ⊓ X.Q 0)) X.QT X.Vone
    (by
      rw [Subgroup.commutator_comm]
      exact commutator_QT_VnegOne_le_Vone X hb hc hGT hs hodd h5 hX)
    (by
      rw [Subgroup.commutator_comm]
      exact commutator_QT_conj_Vone_le_Vone X hb hc hGT hs hodd h5 hX)
    hBnorm hAtauNorm
  simpa [Subgroup.commutator_comm] using h

private theorem relIndex_Q_zero_S_eq_two (hn0 : X.n 0 = 1) :
    (X.Q 0).relIndex X.S = 2 := by
  rw [← X.edgeSylow_zero, X.relIndex_Q_edgeSylow 0, hn0]
  norm_num

private theorem relIndex_Q_one_S_eq_four (hn1 : X.n 1 = 2) :
    (X.Q 1).relIndex X.S = 4 := by
  rw [← X.edgeSylow_zero]
  have h := X.relIndex_Q_succ_edgeSylow (i := 0)
  simpa [hn1] using h

private theorem card_Z_one_eq_two (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) : Nat.card ↥(X.Z 1) = 2 := by
  rw [X.card_Z_one hb hc hGT hs hodd h5 hX, hn0]
  norm_num

private theorem K_fixes_neighbours_zero (hn0 : X.n 0 = 1) :
    ∀ k ∈ X.K, ∀ x : V, Γ.Adj (X.vert 0) x → k • x = x := by
  intro k hk x hx
  by_cases hx1 : x = X.vert 1
  · subst x
    exact X.K_fix k hk 1
  by_cases hxm1 : x = X.vert (-1)
  · subst x
    exact X.K_fix k hk (-1)
  · set D : Set V := Γ.neighborSet (X.vert 0) \ {X.vert 1, X.vert (-1)} with hDdef
    have hDcard : D.ncard = 1 := by
      have h := ncard_neighborSet_diff_two X.hyp (X.adj 0)
        (by simpa using (X.adj (-1)).symm)
        (X.vert_injective.ne (by norm_num : (1 : ℤ) ≠ -1))
      simpa [D, hn0] using h
    have hxmem : x ∈ D := by
      refine ⟨hx, ?_⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hx1, hxm1⟩
    have hkmem : k • x ∈ D := by
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.mem_neighborSet]
        have hk0 : k • X.vert 0 = X.vert 0 := X.K_fix k hk 0
        rw [← hk0]
        exact (X.hyp.adj_smul k (X.vert 0) x).mpr hx
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        constructor
        · intro h
          have h' := congrArg (fun y => k⁻¹ • y) h
          have hxeq : x = X.vert 1 := by
            simpa [X.K_fix k⁻¹ (X.K.inv_mem hk) 1] using h'
          exact hx1 hxeq
        · intro h
          have h' := congrArg (fun y => k⁻¹ • y) h
          have hxeq : x = X.vert (-1) := by
            simpa [X.K_fix k⁻¹ (X.K.inv_mem hk) (-1)] using h'
          exact hxm1 hxeq
    haveI : Finite D := (X.hyp.finite_neighborSet (X.vert 0)).sdiff
    have hsub : D.Subsingleton := Set.ncard_le_one_iff_subsingleton.mp (by omega)
    exact hsub hkmem hxmem

theorem centralizer_transitive_zero (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {q : G} (hq : q ∈ X.QT) :
    ∀ a b : V, Γ.Adj (X.vert 0) a → Γ.Adj (X.vert 0) b →
      ∃ g ∈ Subgroup.centralizer ({q} : Set G) ⊓ X.Gi 0, g • a = b := by
  have hU : X.IsSK X.QT :=
    isSK_QT X hGT hs hodd h5 hX
  have hP : X.skP X.QT ≠ ⊥ ∨ X.n 0 = 2 := by
    left
    intro h
    exact X.QT_ne_bot hGT (le_bot_iff.mp (h ▸ X.QT_le_skP))
  have hUmax : X.IsSKMax X.QT :=
    isSKMax_QT X hGT hs hodd h5 hX
  have hP' : ¬ X.skP X.QT ≤ X.Q 0 ∨ 2 ≤ X.n 0 :=
    X.not_skP_le_Q_zero_or_of_isSKMax hUmax (hP.imp_right Eq.ge)
  have hLstC : X.Lst X.QT 0 ≤ Subgroup.centralizer ({q} : Set G) := by
    have hcomm : ⁅X.Lst X.QT 0, X.QT⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, commutator_QT_Lst_eq_bot X hGT hs hodd h5 hX]
    have h1 : X.Lst X.QT 0 ≤ Subgroup.centralizer (X.QT : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    exact h1.trans (Subgroup.centralizer_le (by simpa using hq))
  have hKfix : ∀ k ∈ X.K, ∀ x : V, Γ.Adj (X.vert 0) x → k • x = x :=
    K_fixes_neighbours_zero X hn0
  intro a b ha hb'
  obtain ⟨g, hgM, hgab⟩ := hU.trans0 a b ha hb'
  have hM : X.normGi X.QT 0 = X.Lst X.QT 0 ⊔ X.K :=
    X.normGi_eq_Lst_sup_K hU hP'
  have hKnorm : X.K ≤ Subgroup.normalizer (X.Lst X.QT 0 : Set G) :=
    (hU.K_le_normGi 0).trans (le_normalizer_oTwoPrime (X.normGi X.QT 0))
  rw [hM] at hgM
  obtain ⟨l, hl, k, hk, hlk⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hKnorm).mp hgM
  have hlM : l ∈ X.normGi X.QT 0 := hM.symm ▸ Subgroup.mem_sup_left hl
  refine ⟨l, ⟨hLstC hl, (X.normGi_le_Gi X.QT 0) hlM⟩, ?_⟩
  calc l • a = l • (k • a) := by rw [hKfix k hk a ha]
    _ = (l * k) • a := by rw [mul_smul]
    _ = g • a := by rw [hlk]
    _ = b := hgab

theorem not_centralizer_transitive_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {q : G} (hq : q ∈ X.QT)
    (hq1 : q ≠ 1) :
    ¬ (∀ a b : V, Γ.Adj (X.vert 1) a → Γ.Adj (X.vert 1) b →
      ∃ g ∈ Subgroup.centralizer ({q} : Set G) ⊓ X.Gi 1, g • a = b) := by
  intro htrans
  have hq0 : q ∈ X.Gi 0 := X.Q_le_Gi 0 (X.QT_le_Q 0 hq)
  have hq1' : q ∈ X.Gi 1 := X.Q_le_Gi 1 (X.QT_le_Q 1 hq)
  have hXq : Subgroup.zpowers q ≤ X.Gi 0 ⊓ X.Gi 1 :=
    Subgroup.zpowers_le.mpr ⟨hq0, hq1'⟩
  have hCz : Subgroup.centralizer ({q} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers q : Set G)) :=
    (CFSG.BlockBasics.centralizer_zpowers_eq_centralizer_singleton q).ge
  have hα : ∀ a b : V, Γ.Adj (X.vert 0) a → Γ.Adj (X.vert 0) b →
      ∃ g ∈ Subgroup.normalizer ((Subgroup.zpowers q : Set G)) ⊓ X.Gi 0, g • a = b := by
    intro a b ha hb0
    obtain ⟨g, hg, hgab⟩ :=
      X.centralizer_transitive_zero hGT hs hodd h5 hX hn0 hq a b ha hb0
    exact ⟨g, ⟨Subgroup.centralizer_le_normalizer _ (hCz hg.1), hg.2⟩, hgab⟩
  have hβ : ∀ a b : V, Γ.Adj (X.vert 1) a → Γ.Adj (X.vert 1) b →
      ∃ g ∈ Subgroup.normalizer ((Subgroup.zpowers q : Set G)) ⊓ X.Gi 1, g • a = b := by
    intro a b ha hb
    obtain ⟨g, hg, hgab⟩ := htrans a b ha hb
    exact ⟨g, ⟨Subgroup.centralizer_le_normalizer _ (hCz hg.1), hg.2⟩, hgab⟩
  have hbot := eq_bot_of_normalizer_trans X.hyp (X.adj 0) hXq hα hβ
  exact hq1 (Subgroup.zpowers_eq_bot.mp hbot)

theorem S_eq_inf_sup_Q_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) :
    X.S = (X.VnegOne ⊓ X.Q 0) ⊔ X.Q 1 := by
  have hS : X.S = X.Q 0 ⊔ X.Q 1 := by
    rw [← X.edgeSylow_zero, ← X.sup_Q_eq_edgeSylow hc 0]
    norm_num
  have hQ := X.Q_zero_eq_sup hb hc hGT hs hodd h5 hX
  have hA : X.Vone ⊓ X.Q 0 ≤ X.Q 1 :=
    inf_le_left.trans (X.Vone_le_Q_one hGT hs hodd h5 hX)
  have hC : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 1 := inf_le_left
  calc X.S = X.Q 0 ⊔ X.Q 1 := hS
    _ = ((X.Vone ⊓ X.Q 0) ⊔ (X.VnegOne ⊓ X.Q 0) ⊔
          (X.Q 1 ⊓ X.Q (-1))) ⊔ X.Q 1 := by
        conv_lhs => rw [hQ]
    _ = (X.VnegOne ⊓ X.Q 0) ⊔ X.Q 1 := by
      refine le_antisymm ?_ ?_
      · refine sup_le (sup_le (sup_le (hA.trans le_sup_right) le_sup_left)
          (hC.trans le_sup_right)) le_sup_right
      · exact sup_le ((le_sup_right.trans le_sup_left).trans le_sup_left) le_sup_right

theorem edgeSylow_one_eq_conj_sup_Q_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) :
    X.edgeSylow 1 = conjSub X.τ (X.Vone ⊓ X.Q 0) ⊔ X.Q 1 := by
  have hQ0 : conjSub X.τ (X.Q 0) = X.Q 2 := by
    simpa [pow_one] using (X.Q_add 1 0).symm
  have hQ1 : conjSub X.τ (X.Q 1) = X.Q 3 := by
    simpa [pow_one] using (X.Q_add 1 1).symm
  have hQm1 : conjSub X.τ (X.Q (-1)) = X.Q 1 := by
    simpa [pow_one] using (X.Q_add 1 (-1)).symm
  have hQ2 : X.Q 2 = (conjSub X.τ X.Vone ⊓ X.Q 2) ⊔
      (conjSub X.τ X.VnegOne ⊓ X.Q 2) ⊔ (X.Q 3 ⊓ X.Q 1) := by
    calc X.Q 2 = conjSub X.τ (X.Q 0) := hQ0.symm
      _ = conjSub X.τ ((X.Vone ⊓ X.Q 0) ⊔ (X.VnegOne ⊓ X.Q 0) ⊔
            (X.Q 1 ⊓ X.Q (-1))) := by
          conv_lhs => rw [X.Q_zero_eq_sup hb hc hGT hs hodd h5 hX]
      _ = (conjSub X.τ X.Vone ⊓ X.Q 2) ⊔
            (conjSub X.τ X.VnegOne ⊓ X.Q 2) ⊔ (X.Q 3 ⊓ X.Q 1) := by
          rw [conjSub_sup, conjSub_sup, conjSub_inf, conjSub_inf, conjSub_inf,
            hQ0, hQ1, hQm1]
  have hB : conjSub X.τ X.VnegOne ⊓ X.Q 2 ≤ X.Q 1 := by
    rw [← hQ0, ← conjSub_inf]
    exact (conjSub_mono X.τ inf_le_left).trans
      (conjSub_tau_VnegOne_le_Q_one X hb hGT hs hodd h5 hX)
  have hC : X.Q 3 ⊓ X.Q 1 ≤ X.Q 1 := inf_le_right
  calc X.edgeSylow 1 = X.Q 1 ⊔ X.Q 2 := (X.sup_Q_eq_edgeSylow hc 1).symm
    _ = X.Q 1 ⊔ ((conjSub X.τ X.Vone ⊓ X.Q 2) ⊔
          (conjSub X.τ X.VnegOne ⊓ X.Q 2) ⊔ (X.Q 3 ⊓ X.Q 1)) := by
        conv_lhs => rw [hQ2]
    _ = conjSub X.τ (X.Vone ⊓ X.Q 0) ⊔ X.Q 1 := by
      conv_rhs => rw [conjSub_inf, hQ0]
      refine le_antisymm ?_ ?_
      · refine sup_le le_sup_right (sup_le (sup_le le_sup_left
          (hB.trans le_sup_right)) (hC.trans le_sup_right))
      · exact sup_le ((le_sup_left.trans le_sup_left).trans le_sup_right) le_sup_left

theorem card_centralizer_VnegOne_le_two (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {q : G} (hq : q ∈ X.QT) :
    Nat.card ↥(X.VnegOne ⊓ X.Q 0) ≤
      2 * Nat.card ↥(X.VnegOne ⊓ X.Q 0 ⊓ Subgroup.centralizer ({q} : Set G)) := by
  have hq' : X.τ * q * X.τ⁻¹ ∈ X.QT :=
    (Subgroup.mem_normalizer_iff.mp X.tau_mem_normalizer_QT q).mp hq
  have hBτV : conjSub X.τ (X.VnegOne ⊓ X.Q 0) ≤ X.Vone :=
    (conjSub_mono X.τ inf_le_left).trans
      (conjSub_tau_VnegOne_le_Vone X)
  have hZ1 : ⁅X.Vone, X.Q 1⁆ = X.Z 1 :=
    commutator_Vone_Q_one X hb hc hGT hs hodd h5 hX
  have hq'Q1 : X.τ * q * X.τ⁻¹ ∈ X.Q 1 := X.QT_le_Q 1 hq'
  have hcomm : ∀ a ∈ conjSub X.τ (X.VnegOne ⊓ X.Q 0), ⁅a, X.τ * q * X.τ⁻¹⁆ ∈ X.Z 1 := by
    intro a ha
    rw [← hZ1]
    exact Subgroup.commutator_mem_commutator (hBτV ha) hq'Q1
  have hZ : Nat.card ↥(X.Z 1) ≤ 2 :=
    (card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0).le
  haveI : Finite ↥(conjSub X.τ (X.VnegOne ⊓ X.Q 0)) :=
    finite_of_le_stabilizer X.hyp (H := conjSub X.τ (X.VnegOne ⊓ X.Q 0))
      (hBτV.trans ((X.Vone_le_Q_one hGT hs hodd h5 hX).trans
        (X.Q_le_Gi 1)))
  have hbound := card_le_two_of_commutator (X := X)
    (A := conjSub X.τ (X.VnegOne ⊓ X.Q 0)) (q := X.τ * q * X.τ⁻¹) hZ hcomm
  have hqeq : q = X.τ⁻¹ * (X.τ * q * X.τ⁻¹) * X.τ := by group
  have hfinal := card_conj_le_two
    (A := conjSub X.τ (X.VnegOne ⊓ X.Q 0))
    (q' := X.τ * q * X.τ⁻¹) (q := q) X.τ⁻¹ (by simpa using hqeq) hbound
  have hAinv : conjSub X.τ⁻¹ (conjSub X.τ (X.VnegOne ⊓ X.Q 0)) =
      X.VnegOne ⊓ X.Q 0 := by
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  rwa [hAinv] at hfinal

theorem card_centralizer_conj_Vone_le_two (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {q : G} (hq : q ∈ X.QT) :
    Nat.card (conjSub X.τ (X.Vone ⊓ X.Q 0)) ≤
      2 * Nat.card ↥(conjSub X.τ (X.Vone ⊓ X.Q 0) ⊓ Subgroup.centralizer ({q} : Set G)) := by
  have hτinv : X.τ⁻¹ ∈ Subgroup.normalizer (X.QT : Set G) :=
    Subgroup.inv_mem _ X.tau_mem_normalizer_QT
  have hq' : X.τ⁻¹ * q * X.τ ∈ X.QT := by
    simpa using (Subgroup.mem_normalizer_iff.mp hτinv q).mp hq
  have hZ1 : ⁅X.Vone, X.Q 1⁆ = X.Z 1 :=
    commutator_Vone_Q_one X hb hc hGT hs hodd h5 hX
  have hq'Q1 : X.τ⁻¹ * q * X.τ ∈ X.Q 1 := X.QT_le_Q 1 hq'
  have hcomm : ∀ a ∈ X.Vone ⊓ X.Q 0, ⁅a, X.τ⁻¹ * q * X.τ⁆ ∈ X.Z 1 := by
    intro a ha
    rw [← hZ1]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_inf.mp ha).1 hq'Q1
  have hZ : Nat.card ↥(X.Z 1) ≤ 2 :=
    (card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0).le
  haveI : Finite ↥(X.Vone ⊓ X.Q 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Vone ⊓ X.Q 0)
      (inf_le_left.trans ((X.Vone_le_Q_one hGT hs hodd h5 hX).trans
        (X.Q_le_Gi 1)))
  have hbound := card_le_two_of_commutator (X := X)
    (A := X.Vone ⊓ X.Q 0) (q := X.τ⁻¹ * q * X.τ) hZ hcomm
  have hqeq : q = X.τ * (X.τ⁻¹ * q * X.τ) * X.τ⁻¹ := by group
  exact card_conj_le_two (A := X.Vone ⊓ X.Q 0)
    (q' := X.τ⁻¹ * q * X.τ) (q := q) X.τ (by simpa using hqeq) hbound

private theorem card_Vone_inf_Q_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hV : Nat.card X.Vone = 32) :
    Nat.card ↥(X.Vone ⊓ X.Q 0) = 16 := by
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
  have hQ0S : (X.Q 0).relIndex X.S = 2 := relIndex_Q_zero_S_eq_two X hn0
  have hSsup : X.S = X.Vone ⊔ X.Q 0 :=
    S_eq_Vone_sup_Q_zero X hb hc hGT hs hodd h5 hX
  have hQ0leS : X.Q 0 ≤ X.S := by rw [hSsup]; exact le_sup_right
  have hQ0normS : ((X.Q 0).subgroupOf X.S).Normal :=
    Subgroup.normal_of_index_eq_two (by simpa [Subgroup.relIndex] using hQ0S)
  have hSnorm : X.S ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ0leS).mp hQ0normS
  have hVnorm : ∀ b ∈ X.Vone, ∀ n ∈ X.Q 0, b * n * b⁻¹ ∈ X.Q 0 := by
    intro b hbV n hn
    exact (Subgroup.mem_normalizer_iff.mp
      (hSnorm (hSsup ▸ Subgroup.mem_sup_left hbV)) n).mp hn
  have hcardS : Nat.card X.S = 2 * Nat.card (X.Q 0) := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.S)
    rw [hQ0S, inf_of_le_left hQ0leS] at h
    exact h.symm
  have hprod := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
    X.Vone (X.Q 0) hVnorm
  rw [← hSsup, hcardS, hV] at hprod
  have h16 : (2 * Nat.card (X.Q 0)) * Nat.card ↥(X.Vone ⊓ X.Q 0) =
      (2 * Nat.card (X.Q 0)) * 16 := by
    rw [hprod]
    ring
  exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by norm_num) Nat.card_pos) h16

private theorem card_Z_zero_eq_four (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) : Nat.card (X.Z 0) = 4 := by
  have h := (X.natQuot_Z_zero hb hc hGT hs hodd h5 hX).index
  rw [Subgroup.relIndex_bot_left, hn0] at h
  simpa using h

private theorem Z_one_lt_Z_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) : X.Z 1 < X.Z 0 := by
  have hle : X.Z 1 ≤ X.Z 0 :=
    le_sup_left.trans
      (Z_zero_eq_Z_one_sup_Z_neg_one X hb hc hGT hs hodd h5 hX).ge
  refine lt_of_le_of_ne hle ?_
  intro heq
  have h1 : Nat.card (X.Z 1) = 2 :=
    card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0
  have h0 := card_Z_zero_eq_four X hb hc hGT hs hodd h5 hX hn0
  have hc' : Nat.card (X.Z 1) = Nat.card (X.Z 0) := by rw [heq]
  omega

private theorem Z_zero_sq (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {z : G} (hz : z ∈ X.Z 0) : z ^ 2 = 1 := by
  have hZ0 := Z_zero_eq_Z_one_sup_Z_neg_one X hb hc hGT hs hodd h5 hX
  have hmem : z ∈ X.Z 1 ⊔ X.Z (-1) := by rwa [← hZ0]
  have hZ1norm : X.Z 1 ≤ Subgroup.normalizer (X.Z (-1) : Set G) := by
    refine (show X.Z 1 ≤ Subgroup.centralizer (X.Z (-1) : Set G) from ?_).trans
      (Subgroup.centralizer_le_normalizer _)
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have haQ : a ∈ X.Q 0 := X.Z_le_Q 0 (hZ0 ▸ Subgroup.mem_sup_left ha)
    have hbQ : b ∈ X.Q 0 := X.Z_le_Q 0 (hZ0 ▸ Subgroup.mem_sup_right hb)
    have haC : a ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 0 (hZ0 ▸ Subgroup.mem_sup_left ha))).2
    exact (Subgroup.mem_centralizer_iff.mp haC b hbQ)
  obtain ⟨a, ha, b, hb1, hzab⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hZ1norm).mp hmem
  have hcard1 : Nat.card ↥(X.Z 1) = 2 :=
    card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0
  have hcardm1 : Nat.card ↥(X.Z (-1)) = 2 := by
    have h := card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0
    have hconj : conjSub X.τ⁻¹ (X.Z 1) = X.Z (-1) := by
      have hτ : X.τ⁻¹ • X.vert 1 = X.vert (-1) := by
        simpa using X.zpow_smul_vert (-1) 1
      exact X.Z_conj hτ
    have hcm : Nat.card ↥(conjSub X.τ⁻¹ (X.Z 1)) = Nat.card ↥(X.Z 1) :=
      CFSG.Quasithin.St84.card_conjSub X.τ⁻¹ (X.Z 1)
    rw [← hconj, hcm]
    simpa using h
  have ha2 : a ^ 2 = 1 := by
    have hdiv : orderOf (⟨a, ha⟩ : ↥(X.Z 1)) ∣ 2 := hcard1 ▸ orderOf_dvd_natCard _
    have hdiv' : orderOf a ∣ 2 := by rwa [Subgroup.orderOf_mk a ha] at hdiv
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv'
  have hb2 : b ^ 2 = 1 := by
    have hdiv : orderOf (⟨b, hb1⟩ : ↥(X.Z (-1))) ∣ 2 := hcardm1 ▸ orderOf_dvd_natCard _
    have hdiv' : orderOf b ∣ 2 := by rwa [Subgroup.orderOf_mk b hb1] at hdiv
    exact orderOf_dvd_iff_pow_eq_one.mp hdiv'
  have haQ : a ∈ X.Q 0 := X.Z_le_Q 0 (hZ0 ▸ Subgroup.mem_sup_left ha)
  have hbQ : b ∈ X.Q 0 := X.Z_le_Q 0 (hZ0 ▸ Subgroup.mem_sup_right hb1)
  have hcomm : Commute a b := by
    have haC : a ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
      (Subgroup.mem_inf.mp (X.Z_le_center 0 (hZ0 ▸ Subgroup.mem_sup_left ha))).2
    exact (Subgroup.mem_centralizer_iff.mp haC b hbQ).symm
  rw [hzab]
  calc (a * b) ^ 2 = a ^ 2 * b ^ 2 := hcomm.mul_pow 2
    _ = 1 := by rw [ha2, hb2, mul_one]

private theorem isElemSec_Z_one_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) : IsElemSec (X.Z 1) X.Vone := by
  have hVQ1 : X.Vone ≤ X.Q 1 :=
    X.Vone_le_Q_one hGT hs hodd h5 hX
  have hZ1V : X.Z 1 ≤ X.Vone := by
    calc X.Z 1 ≤ X.Z 0 := (Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le
      _ ≤ X.Vone := Z_zero_le_Vone X
  have hcomm : ⁅X.Vone, X.Vone⁆ ≤ X.Z 1 := by
    have h := commutator_Vone_Q_one X hb hc hGT hs hodd h5 hX
    calc ⁅X.Vone, X.Vone⁆ ≤ ⁅X.Vone, X.Q 1⁆ := Subgroup.commutator_mono le_rfl hVQ1
      _ = X.Z 1 := h
  have hcent : X.Z 1 ≤ Subgroup.centralizer (X.Vone : Set G) :=
    ((X.Z_le_center 1).trans inf_le_right).trans (Subgroup.centralizer_le hVQ1)
  refine ⟨hZ1V, hcomm, ?_⟩
  let W : Subgroup G :=
    { carrier := {x : G | x ∈ X.Vone ∧ x ^ 2 ∈ X.Z 1}
      one_mem' := ⟨X.Vone.one_mem, by simp⟩
      mul_mem' := by
        rintro a b ⟨haV, ha2⟩ ⟨hbV, hb2⟩
        refine ⟨X.Vone.mul_mem haV hbV, ?_⟩
        have hab1 : ⁅a, b⁆ ∈ X.Z 1 :=
          hcomm (Subgroup.commutator_mem_commutator haV hbV)
        have ha2' : a * a ∈ X.Z 1 := by simpa [pow_two] using ha2
        have hb2' : b * b ∈ X.Z 1 := by simpa [pow_two] using hb2
        have hacent : b * (a * a) * b = (a * a) * (b * b) := by
          have hc' : (a * a) * b = b * (a * a) :=
            (Subgroup.mem_centralizer_iff.mp (hcent ha2') b hbV).symm
          calc b * (a * a) * b = ((a * a) * b) * b := by rw [hc']
            _ = (a * a) * (b * b) := by rw [mul_assoc]
        have hstep : (a * b) * (a * b) = ⁅a, b⁆ * ((a * a) * (b * b)) := by
          calc (a * b) * (a * b) = (⁅a, b⁆ * (b * a)) * (a * b) := by
                rw [show a * b = ⁅a, b⁆ * (b * a) from by
                  rw [commutatorElement_def]; group]
            _ = ⁅a, b⁆ * (b * (a * a) * b) := by group
            _ = ⁅a, b⁆ * ((a * a) * (b * b)) := by rw [hacent]
        rw [pow_two]
        rw [hstep]
        have hz : (a * a) * (b * b) ∈ X.Z 1 := (X.Z 1).mul_mem ha2' hb2'
        exact (X.Z 1).mul_mem hab1 hz
      inv_mem' := by
        rintro a ⟨haV, ha2⟩
        refine ⟨X.Vone.inv_mem haV, ?_⟩
        have ha2' : a * a ∈ X.Z 1 := by simpa [pow_two] using ha2
        rw [pow_two]
        simpa [mul_inv] using (X.Z 1).inv_mem ha2' }
  have hVleW : X.Vone ≤ W := by
    unfold Setup.Vone
    refine iSup_le fun g => iSup_le fun hg => ?_
    intro x hx
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hx
    rw [← hzx]
    refine ⟨?_, ?_⟩
    · exact Subgroup.mem_iSup_of_mem g (Subgroup.mem_iSup_of_mem hg
        (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hz))
    · have hz2 : z ^ 2 = 1 := Z_zero_sq X hb hc hGT hs hodd h5 hX hn0 hz
      rw [pow_two]
      have hsq : (MulAut.conj g).toMonoidHom z * (MulAut.conj g).toMonoidHom z = 1 := by
        calc (MulAut.conj g).toMonoidHom z * (MulAut.conj g).toMonoidHom z
            = (MulAut.conj g).toMonoidHom (z * z) := by rw [map_mul]
          _ = (MulAut.conj g).toMonoidHom (z ^ 2) := by rw [pow_two]
          _ = 1 := by rw [hz2, map_one]
      rw [hsq]
      exact (X.Z 1).one_mem
  intro v hv
  exact (hVleW hv).2

private theorem relIndex_Z_one_Vone_eq_sixteen (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2)
    (hirr : ∀ W : Subgroup G, X.Z 1 ≤ W → W ≤ X.Vone →
      X.L 1 ≤ Subgroup.normalizer (W : Set G) → W = X.Z 1 ∨ W = X.Vone)
    (hnt : ∃ l ∈ X.L 1, ∃ v ∈ X.Vone, ⁅l, v⁆ ∉ X.Z 1) :
    (X.Z 1).relIndex X.Vone = 16 := by
  haveI : Finite ↥(X.L 1) :=
    finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hQ1L : X.Q 1 ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi 1)
  have hVH : X.Vone ≤ X.L 1 :=
    (X.Vone_le_Q_one hGT hs hodd h5 hX).trans hQ1L
  have hZH : X.Z 1 ≤ X.L 1 :=
    (Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le.trans
      (Z_zero_le_Vone X) |>.trans hVH
  let H : Subgroup G := X.L 1
  let V' : Subgroup ↥H := X.Vone.subgroupOf H
  let Z' : Subgroup ↥H := (X.Z 1).subgroupOf H
  have hquot : IsL2Quot 2 (oTwoQuot ↥(X.L 1)) := by
    have hN : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
    obtain ⟨e⟩ := hN.quot
    rw [hn1] at e
    exact ⟨e⟩
  have hquot' : IsL2Quot 2 (oTwoQuot ↥(⊤ : Subgroup ↥H)) := by
    obtain ⟨e⟩ := hquot
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr Subgroup.topEquiv).trans e⟩
  have hsec' : IsElemSec Z' V' :=
    isElemSec_subgroupOf (H := H) (Z := X.Z 1) (V := X.Vone)
      (isElemSec_Z_one_Vone X hb hc hGT hs hodd h5 hX hn0)
  have hVZ' : Z' ≤ V' := hsec'.1
  have hL' : (⊤ : Subgroup ↥H) ≤
      Subgroup.normalizer (V' : Set ↥H) ⊓ Subgroup.normalizer (Z' : Set ↥H) :=
    le_inf (le_normalizer_subgroupOf_of_le_normalizer hVH
        ((X.L_le_Gi 1).trans (Gi_one_le_normalizer_Vone X)))
      (le_normalizer_subgroupOf_of_le_normalizer hZH fun x hx =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 x (X.L_le_Gi 1 hx)))
  have hirr' : ∀ W' : Subgroup ↥H, Z' ≤ W' → W' ≤ V' →
      (⊤ : Subgroup ↥H) ≤ Subgroup.normalizer (W' : Set ↥H) →
      W' = Z' ∨ W' = V' := by
    intro W' hZW hWV hWn
    let W : Subgroup G := W'.map H.subtype
    have hZleW : X.Z 1 ≤ W := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hZH]
      exact Subgroup.map_mono hZW
    have hWleV : W ≤ X.Vone := by
      calc W = W'.map H.subtype := rfl
        _ ≤ V'.map H.subtype := Subgroup.map_mono hWV
        _ = X.Vone ⊓ H := Subgroup.subgroupOf_map_subtype _ _
        _ ≤ X.Vone := inf_le_left
    have hWnorm : X.L 1 ≤ Subgroup.normalizer (W : Set G) := by
      refine le_normalizer_of_le_normalizer_subgroupOf (Subgroup.map_subtype_le W') ?_
      have hWW : W.subgroupOf H = W' := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective W'
      rw [hWW]; exact hWn
    rcases hirr W hZleW hWleV hWnorm with h | h
    · left
      refine le_antisymm ?_ hZW
      intro x hx
      have hxW : (x : G) ∈ W := Subgroup.mem_map_of_mem H.subtype hx
      rw [h] at hxW
      exact Subgroup.mem_subgroupOf.mpr hxW
    · right
      refine le_antisymm hWV ?_
      intro v hv
      have hvW : (v : G) ∈ W := by
        rw [h]
        exact Subgroup.mem_subgroupOf.mp hv
      obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp hvW
      have : y = v := Subtype.ext hyv
      rwa [this] at hy
  have hnt' : ∃ l ∈ (⊤ : Subgroup ↥H), ∃ v ∈ V', ⁅l, v⁆ ∉ Z' := by
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    let v' : ↥H := ⟨v, hVH hv⟩
    refine ⟨⟨l, hl⟩, Subgroup.mem_top _, v', Subgroup.mem_subgroupOf.mpr hv, ?_⟩
    intro hmem
    apply hne
    have hm := Subgroup.mem_subgroupOf.mp hmem
    change ⁅((⟨l, hl⟩ : ↥H) : G), (v' : G)⁆ ∈ X.Z 1 at hm
    rw [commutatorElement_def] at hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hm
    simpa [v', commutatorElement_def] using hm
  have hres := card_eq_sixteen_of_irreducible (G := ↥H) (V := V') (Z := Z') (L := ⊤)
    hquot' hVZ' hsec' hL' hirr' hnt'
  have hrel : Z'.relIndex V' = (X.Z 1).relIndex X.Vone :=
    Subgroup.relIndex_subgroupOf (H := X.Z 1) (K := X.Vone) (L := X.L 1) hVH
  rw [← hrel]
  exact hres

private theorem normal_between_inf_Z_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N) (hNV : N ≤ X.Vone) (hNne : N ≠ X.Vone)
    (hNnorm : X.L 1 ≤ Subgroup.normalizer (N : Set G)) :
    N ⊓ X.Z 0 = X.Z 1 := by
  have hlt : X.Z 1 < X.Z 0 := Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0
  have hnotZ0 : ¬ X.Z 0 ≤ N := by
    intro hZ0N
    apply hNne
    have hVleN : X.Vone ≤ N := by
      unfold Setup.Vone
      refine iSup_le fun g => iSup_le fun hg => ?_
      have hgL : g ∈ X.L 1 := by
        rw [← Gi_one_eq_L_one X hb hc hGT hs hodd h5 hX hn0]
        exact hg
      calc conjSub g (X.Z 0) ≤ conjSub g N := conjSub_mono g hZ0N
        _ = N := by
            have hmem := hNnorm hgL
            simpa [conjSub] using Subgroup.mem_normalizer_iff_map_conj_eq.mp hmem
    exact le_antisymm hNV hVleN
  let M : Subgroup G := N ⊓ X.Z 0
  have hZ1M : X.Z 1 ≤ M := le_inf hZ1N hlt.le
  have hMZ : M ≤ X.Z 0 := inf_le_right
  have hrel0 : (X.Z 1).relIndex (X.Z 0) = 2 := by
    have h0 : Nat.card (X.Z 0) = 4 := card_Z_zero_eq_four X hb hc hGT hs hodd h5 hX hn0
    have h1 : Nat.card (X.Z 1) = 2 :=
      card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0
    have h := Subgroup.relIndex_mul_card (H := X.Z 1) (K := X.Z 0)
    rw [inf_of_le_left hlt.le, h0, h1] at h
    omega
  by_cases hM1 : M = X.Z 1
  · exact hM1
  · exfalso
    have hMneZ0 : M ≠ X.Z 0 := by
      intro h; exact hnotZ0 (h ▸ inf_le_left)
    have hrelM_ne1 : (X.Z 1).relIndex M ≠ 1 := by
      intro h1
      have hle : M ≤ X.Z 1 := Subgroup.relIndex_eq_one.mp h1
      exact hM1 (le_antisymm hle hZ1M)
    have htower : (X.Z 1).relIndex M * M.relIndex (X.Z 0) = 2 := by
      rw [Subgroup.relIndex_mul_relIndex (H := X.Z 1) (K := M) (L := X.Z 0) hZ1M hMZ, hrel0]
    have hdvd : (X.Z 1).relIndex M ∣ 2 := ⟨M.relIndex (X.Z 0), htower.symm⟩
    have hrelM2 : (X.Z 1).relIndex M = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd h1 hrelM_ne1
      · exact h2
    have hMrel : M.relIndex (X.Z 0) = 1 := by
      rw [hrelM2] at htower
      omega
    have hZ0leM : X.Z 0 ≤ M := Subgroup.relIndex_eq_one.mp hMrel
    exact hMneZ0 (le_antisymm hMZ hZ0leM)

private theorem commutator_Q_zero_le_inf : ⁅X.Q 0, X.Q 0⁆ ≤ X.Q (-1) ⊓ X.Q 1 := by
  have hQ0S : X.Q 0 ≤ X.edgeSylow (-1) := by simpa using X.Q_le_edgeSylow (-1)
  have hsq : ∀ x ∈ X.Q 0, x ^ 2 ∈ X.Q (-1) ⊓ X.Q 1 := fun x hx => Subgroup.mem_inf.mpr
    ⟨sq_mem_Q_of_relIndex X (S := X.edgeSylow (-1)) (j := -1)
        (X.isSylowTwoOf_edgeSylow_L (-1)).1 (X.relIndex_Q_edgeSylow (-1)) x (hQ0S hx),
     sq_mem_Q_of_relIndex X (S := X.edgeSylow 0) (j := 1)
        (X.isSylowTwoOf_edgeSylow_L_succ 0).1 (X.relIndex_Q_succ_edgeSylow 0) x
        (X.Q_le_edgeSylow_left 0 hx)⟩
  rw [Subgroup.commutator_le]
  intro x hx y hy
  rw [show ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * y⁻¹ ^ 2 by
    simp only [commutatorElement_def, pow_two]; group]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hsq x hx)
    (hsq _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hx) hy))) (hsq _ (Subgroup.inv_mem _ hy))

private theorem normal_between_le_Q_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) {N : Subgroup G}
    (hNV : N ≤ X.Vone)
    (hNcomm : ⁅N, X.L 1⁆ ≤ X.Z 1) : N ≤ X.Q 0 := by
  by_contra hNQ
  obtain ⟨n, hnN, hnQ0⟩ := Set.not_subset.mp hNQ
  have hVQ1 : X.Vone ≤ X.Q 1 :=
    X.Vone_le_Q_one hGT hs hodd h5 hX
  have hnQ1 : n ∈ X.Q 1 := hVQ1 (hNV hnN)
  let C : Subgroup G := X.Q (-1) ⊓ X.Q 1
  let A : Subgroup G := X.Q 0 ⊓ X.Q 1
  have hCQ0 : C ≤ X.Q 0 := (inf_comm (X.Q (-1)) (X.Q 1)).le.trans
    (le_sup_right.trans (Q_zero_eq_sup X hb hc hGT hs hodd h5 hX).ge)
  have hCA : C ≤ A := by
    dsimp [A, C]
    exact le_inf hCQ0 inf_le_right
  have hAA' : A ≤ X.Q 1 := inf_le_right
  have hA0 : X.Gi 0 ≤ Subgroup.normalizer ((X.Q (-1) ⊓ X.Q 1 : Subgroup G) : Set G) := by
    have h := Q_one_inf_neg_one_normal X hb hc hGT hs hodd h5 hX
    simpa [inf_comm] using h
  obtain ⟨hQ0eq, hrelQ0, hrelA, -, hgen⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  have hrelA4 : C.relIndex A = 4 := by
    dsimp [C, A]
    rw [hrelA, hn1]
    norm_num
  have hcomm_not : ¬ ⁅X.Q 0, X.Q 1⁆ ≤ C := by
    intro h
    have hB : ⁅X.Q 0 ⊓ X.Q (-1), X.Q 1⁆ ≤ C :=
      (Subgroup.commutator_mono inf_le_left le_rfl).trans h
    have hAleC : A ≤ C := le_trans hgen (sup_le hB le_rfl)
    have heq : C = A := le_antisymm hCA hAleC
    rw [heq, Subgroup.relIndex_self] at hrelA4
    omega
  have hex : ∃ x ∈ X.Q 0, ∃ q ∈ X.Q 1, ⁅x, q⁆ ∉ C := by
    by_contra h
    push Not at h
    exact hcomm_not (Subgroup.commutator_le.mpr h)
  obtain ⟨x, hxQ0, q, hqQ1, hxq⟩ := hex
  have hqA : q ∉ A := by
    intro hqA
    have hqQ0 : q ∈ X.Q 0 := (Subgroup.mem_inf.mp hqA).1
    have hqq : ⁅x, q⁆ ∈ ⁅X.Q 0, X.Q 0⁆ :=
      Subgroup.commutator_mem_commutator hxQ0 hqQ0
    have hle : ⁅X.Q 0, X.Q 0⁆ ≤ C := commutator_Q_zero_le_inf X
    exact hxq (hle hqq)
  have hQ0S : (X.Q 0).relIndex X.S = 2 := relIndex_Q_zero_S_eq_two X hn0
  have hQ1S : (X.Q 1).relIndex X.S = 4 := relIndex_Q_one_S_eq_four X hn1
  have hQ0Sle : X.Q 0 ≤ X.S := by
    rw [← X.edgeSylow_zero]; exact X.Q_le_edgeSylow_left 0
  have hQ1Sle : X.Q 1 ≤ X.S := by
    rw [← X.edgeSylow_zero]; exact X.Q_le_edgeSylow_right 1
  have hCS : C.relIndex X.S = 32 := by
    have h1 : C.relIndex (X.Q 0) * (X.Q 0).relIndex X.S = C.relIndex X.S :=
      Subgroup.relIndex_mul_relIndex (H := C) (K := X.Q 0) (L := X.S) hCQ0 hQ0Sle
    rw [show C.relIndex (X.Q 0) = 16 by dsimp [C]; rw [hrelQ0, hn1]; norm_num,
      hQ0S] at h1
    omega
  have hCQ1 : C.relIndex (X.Q 1) = 8 := by
    have h1 : C.relIndex A * A.relIndex (X.Q 1) = C.relIndex (X.Q 1) :=
      Subgroup.relIndex_mul_relIndex (H := C) (K := A) (L := X.Q 1) hCA hAA'
    rw [hrelA4] at h1
    have h2 : C.relIndex (X.Q 1) * (X.Q 1).relIndex X.S = C.relIndex X.S :=
      Subgroup.relIndex_mul_relIndex (H := C) (K := X.Q 1) (L := X.S)
        (show C ≤ X.Q 1 from inf_le_right) hQ1Sle
    rw [hCS, hQ1S] at h2
    omega
  have hAreq : A.relIndex (X.Q 1) = 2 := by
    have h1 : C.relIndex A * A.relIndex (X.Q 1) = C.relIndex (X.Q 1) :=
      Subgroup.relIndex_mul_relIndex (H := C) (K := A) (L := X.Q 1) hCA hAA'
    rw [hrelA4, hCQ1] at h1
    omega
  obtain ⟨a, haQ1, haxor⟩ := (Subgroup.relIndex_eq_two_iff.mp hAreq)
  have hnA : n ∉ A := by
    intro hnA
    exact hnQ0 (Subgroup.mem_inf.mp hnA).1
  have hqaA : q * a ∈ A := by
    have h := haxor q hqQ1
    rw [xor_iff_or_and_not_and] at h
    rcases h.1 with h | h
    · exact h
    · exact absurd h hqA
  have hnaA : n * a ∈ A := by
    have h := haxor n hnQ1
    rw [xor_iff_or_and_not_and] at h
    rcases h.1 with h | h
    · exact h
    · exact absurd h hnA
  let a0 : G := (n * a) * (q * a)⁻¹
  have ha0A : a0 ∈ A := A.mul_mem hnaA (A.inv_mem hqaA)
  have hna0 : n = a0 * q := by
    dsimp [a0]
    group
  have hxa0 : ⁅x, a0⁆ ∈ C := by
    have h1 : ⁅x, a0⁆ ∈ ⁅X.Q 0, X.Q 0⁆ :=
      Subgroup.commutator_mem_commutator hxQ0 (Subgroup.mem_inf.mp ha0A).1
    exact commutator_Q_zero_le_inf X h1
  have ha0N : a0 ∈ Subgroup.normalizer (C : Set G) :=
    hA0 (X.Q_le_Gi 0 (Subgroup.mem_inf.mp ha0A).1)
  have hformula : ⁅x, a0 * q⁆ = ⁅x, a0⁆ * (a0 * ⁅x, q⁆ * a0⁻¹) := by
    rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
    group
  have hxq' : ⁅x, n⁆ ∉ C := by
    rw [hna0, hformula]
    intro h
    have hwx : a0 * ⁅x, q⁆ * a0⁻¹ ∈ C := by
      have h' : ⁅x, a0⁆⁻¹ * (⁅x, a0⁆ * (a0 * ⁅x, q⁆ * a0⁻¹)) ∈ C :=
        C.mul_mem (C.inv_mem hxa0) h
      have h'' : ⁅x, a0⁆⁻¹ * (⁅x, a0⁆ * (a0 * ⁅x, q⁆ * a0⁻¹)) =
          a0 * ⁅x, q⁆ * a0⁻¹ := by group
      rwa [h''] at h'
    have hxqC : ⁅x, q⁆ ∈ C := by
      have h' := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha0N)
        (a0 * ⁅x, q⁆ * a0⁻¹)).mp hwx
      simpa [mul_assoc] using h'
    exact hxq hxqC
  have hZ1C : X.Z 1 ≤ C := by
    refine le_inf ?_ (X.Z_le_Q 1)
    exact (Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le.trans
      (Z_zero_le_Q_neg_one X hb hGT hs hodd h5 hX)
  have hxqC2 : ⁅x, n⁆ ∈ C := by
    have hmem : ⁅x, n⁆ ∈ ⁅X.Q 0, N⁆ := Subgroup.commutator_mem_commutator hxQ0 hnN
    have hQ0L : X.Q 0 ≤ X.L 1 :=
      (X.Q_le_edgeSylow_left 0).trans (X.isSylowTwoOf_edgeSylow_L_succ 0).1
    have hle : ⁅X.Q 0, N⁆ ≤ X.Z 1 := by
      rw [Subgroup.commutator_comm]
      exact (Subgroup.commutator_mono le_rfl hQ0L).trans hNcomm
    exact hZ1C (hle hmem)
  exact hxq' hxqC2

private theorem normal_between_commutator_inf_Q_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {N : Subgroup G}
    (hNV : N ≤ X.Vone)
    (hNZ0 : N ⊓ X.Z 0 = X.Z 1)
    (hNnorm : X.L 1 ≤ Subgroup.normalizer (N : Set G)) :
    ⁅N ⊓ X.Q (-1), X.Q 0⁆ ≤ X.Z 1 := by
  have hNnorm' : ⁅N, X.L 1⁆ ≤ N :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hNnorm
  have hVQ1 : X.Vone ≤ X.Q 1 :=
    X.Vone_le_Q_one hGT hs hodd h5 hX
  have hQ0L : X.Q 0 ≤ X.L 1 :=
    (X.Q_le_edgeSylow_left 0).trans (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hZ0normal : X.Gi 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact X.Z_normal 0 g hg
  have hVcomm : ⁅X.Vone, X.Vone⁆ ≤ X.Z 1 := by
    have h := commutator_Vone_Q_one X hb hc hGT hs hodd h5 hX
    calc ⁅X.Vone, X.Vone⁆ ≤ ⁅X.Vone, X.Q 1⁆ := Subgroup.commutator_mono le_rfl hVQ1
      _ = X.Z 1 := h
  have hBcomm : ⁅X.Q (-1), X.VnegOne⁆ ≤ X.Z (-1) := by
    rw [Subgroup.commutator_comm]
    exact commutator_VnegOne_Q_neg_one_le X hb hc hGT hs hodd h5 hX
  have hZnegZ0 : X.Z (-1) ≤ X.Z 0 :=
    le_sup_right.trans
      (Z_zero_eq_Z_one_sup_Z_neg_one X hb hc hGT hs hodd h5 hX).ge
  have hZ1Z0 : X.Z 1 ≤ X.Z 0 :=
    (Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le
  rw [Subgroup.commutator_le]
  intro x hx q hq
  obtain ⟨hxN, hxQm⟩ := Subgroup.mem_inf.mp hx
  have hxV : x ∈ X.Vone := hNV hxN
  let H : Subgroup G :=
    { carrier := {y : G | y ∈ X.Q 0 ∧ ⁅x, y⁆ ∈ X.Z 0}
      one_mem' := ⟨(X.Q 0).one_mem, by simp⟩
      mul_mem' := by
        rintro q1 q2 ⟨hq1Q, hq1⟩ ⟨hq2Q, hq2⟩
        refine ⟨(X.Q 0).mul_mem hq1Q hq2Q, ?_⟩
        have hid : ⁅x, q1 * q2⁆ = ⁅x, q1⁆ * (q1 * ⁅x, q2⁆ * q1⁻¹) := by
          rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
          group
        rw [hid]
        have hconj : q1 * ⁅x, q2⁆ * q1⁻¹ ∈ X.Z 0 :=
          (Subgroup.mem_normalizer_iff.mp (hZ0normal (X.Q_le_Gi 0 hq1Q))
            (⁅x, q2⁆)).mp hq2
        exact (X.Z 0).mul_mem hq1 hconj
      inv_mem' := by
        rintro q1 ⟨hq1Q, hq1⟩
        refine ⟨(X.Q 0).inv_mem hq1Q, ?_⟩
        have hid : ⁅x, q1⁻¹⁆ = q1⁻¹ * ⁅x, q1⁆⁻¹ * q1 := by
          simp only [commutatorElement_def]
          group
        rw [hid]
        have hqnorm : q1⁻¹ ∈ Subgroup.normalizer (X.Z 0 : Set G) :=
          Subgroup.inv_mem _ (hZ0normal (X.Q_le_Gi 0 hq1Q))
        simpa using
          (Subgroup.mem_normalizer_iff.mp hqnorm (⁅x, q1⁆⁻¹)).mp ((X.Z 0).inv_mem hq1) }
  have hAle : X.Vone ⊓ X.Q 0 ≤ H := by
    intro a ha
    obtain ⟨haV, haQ⟩ := Subgroup.mem_inf.mp ha
    exact ⟨haQ, hZ1Z0 (hVcomm (Subgroup.commutator_mem_commutator hxV haV))⟩
  have hBle : X.VnegOne ⊓ X.Q 0 ≤ H := by
    intro b hb'
    obtain ⟨hbV, hbQ⟩ := Subgroup.mem_inf.mp hb'
    exact ⟨hbQ, hZnegZ0 (hBcomm (Subgroup.commutator_mem_commutator hxQm hbV))⟩
  have hCle : X.Q 1 ⊓ X.Q (-1) ≤ H := by
    intro c hc'
    obtain ⟨hcQ1, -⟩ := Subgroup.mem_inf.mp hc'
    have h := commutator_Vone_Q_one X hb hc hGT hs hodd h5 hX
    have hcQ0 : c ∈ X.Q 0 :=
      (le_sup_right.trans (Q_zero_eq_sup X hb hc hGT hs hodd h5 hX).ge) hc'
    exact ⟨hcQ0, hZ1Z0 (h ▸ Subgroup.commutator_mem_commutator hxV hcQ1)⟩
  have hQ0H : X.Q 0 ≤ H := by
    have hsup := Q_zero_eq_sup X hb hc hGT hs hodd h5 hX
    rw [hsup]
    exact sup_le (sup_le hAle hBle) hCle
  have hmemZ0 : ⁅x, q⁆ ∈ X.Z 0 := (hQ0H hq).2
  have hmemN : ⁅x, q⁆ ∈ N :=
    hNnorm' (Subgroup.commutator_mem_commutator hxN (hQ0L hq))
  have hmem : ⁅x, q⁆ ∈ N ⊓ X.Z 0 := Subgroup.mem_inf.mpr ⟨hmemN, hmemZ0⟩
  rwa [hNZ0] at hmem

private theorem isElemSec_of_le {Z N V : Subgroup G} (hZN : Z ≤ N) (hNV : N ≤ V)
    (h : IsElemSec Z V) : IsElemSec Z N :=
  ⟨hZN, (Subgroup.commutator_mono hNV hNV).trans h.2.1,
    fun x hx => h.2.2 x (hNV hx)⟩

private theorem sixteen_le_relIndex_of_nontrivial (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N) (hNV : N ≤ X.Vone)
    (hNnorm : X.L 1 ≤ Subgroup.normalizer (N : Set G))
    (hirr : ∀ M : Subgroup G, X.Z 1 ≤ M → M ≤ N →
      X.L 1 ≤ Subgroup.normalizer (M : Set G) → M = X.Z 1 ∨ M = N)
    (hnt : ∃ l ∈ X.L 1, ∃ v ∈ N, ⁅l, v⁆ ∉ X.Z 1) :
    16 ≤ (X.Z 1).relIndex N := by
  haveI : Finite ↥(X.L 1) :=
    finite_of_le_stabilizer X.hyp (H := X.L 1) (X.L_le_Gi 1)
  have hQ1L : X.Q 1 ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi 1)
  have hVH : X.Vone ≤ X.L 1 :=
    (X.Vone_le_Q_one hGT hs hodd h5 hX).trans hQ1L
  have hNH : N ≤ X.L 1 := hNV.trans hVH
  have hZH : X.Z 1 ≤ X.L 1 := hZ1N.trans hNH
  let H : Subgroup G := X.L 1
  let N' : Subgroup ↥H := N.subgroupOf H
  let Z' : Subgroup ↥H := (X.Z 1).subgroupOf H
  have hquot : IsL2Quot 2 (oTwoQuot ↥(X.L 1)) := by
    have hN : IsLocL2 Γ G (X.vert 1) (X.n 1) (X.L 1) := X.hyp.isLocL2_oTwoPrime (X.vert 1)
    obtain ⟨e⟩ := hN.quot
    rw [hn1] at e
    exact ⟨e⟩
  have hquot' : IsL2Quot 2 (oTwoQuot ↥(⊤ : Subgroup ↥H)) := by
    obtain ⟨e⟩ := hquot
    exact ⟨(CFSG.Quasithin.F112R.oTwoQuotCongr Subgroup.topEquiv).trans e⟩
  have hsec' : IsElemSec Z' N' :=
    isElemSec_subgroupOf (H := H) (Z := X.Z 1) (V := N)
      (isElemSec_of_le hZ1N hNV
        (isElemSec_Z_one_Vone X hb hc hGT hs hodd h5 hX hn0))
  have hNZ' : Z' ≤ N' := hsec'.1
  have hL' : (⊤ : Subgroup ↥H) ≤
      Subgroup.normalizer (N' : Set ↥H) ⊓ Subgroup.normalizer (Z' : Set ↥H) :=
    le_inf (le_normalizer_subgroupOf_of_le_normalizer hNH hNnorm)
      (le_normalizer_subgroupOf_of_le_normalizer hZH fun x hx =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal 1 x (X.L_le_Gi 1 hx)))
  have hirr' : ∀ W' : Subgroup ↥H, Z' ≤ W' → W' ≤ N' →
      (⊤ : Subgroup ↥H) ≤ Subgroup.normalizer (W' : Set ↥H) →
      W' = Z' ∨ W' = N' := by
    intro W' hZW hWV hWn
    let W : Subgroup G := W'.map H.subtype
    have hZleW : X.Z 1 ≤ W := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hZH]
      exact Subgroup.map_mono hZW
    have hWleV : W ≤ N := by
      calc W = W'.map H.subtype := rfl
        _ ≤ N'.map H.subtype := Subgroup.map_mono hWV
        _ = N ⊓ H := Subgroup.subgroupOf_map_subtype _ _
        _ ≤ N := inf_le_left
    have hWnorm : X.L 1 ≤ Subgroup.normalizer (W : Set G) := by
      refine le_normalizer_of_le_normalizer_subgroupOf (Subgroup.map_subtype_le W') ?_
      have hWW : W.subgroupOf H = W' := by
        rw [← Subgroup.comap_subtype]
        exact Subgroup.comap_map_eq_self_of_injective H.subtype_injective W'
      rw [hWW]; exact hWn
    rcases hirr W hZleW hWleV hWnorm with h | h
    · left
      refine le_antisymm ?_ hZW
      intro x hx
      have hxW : (x : G) ∈ W := Subgroup.mem_map_of_mem H.subtype hx
      rw [h] at hxW
      exact Subgroup.mem_subgroupOf.mpr hxW
    · right
      refine le_antisymm hWV ?_
      intro v hv
      have hvW : (v : G) ∈ W := by
        rw [h]
        exact Subgroup.mem_subgroupOf.mp hv
      obtain ⟨y, hy, hyv⟩ := Subgroup.mem_map.mp hvW
      have : y = v := Subtype.ext hyv
      rwa [this] at hy
  have hnt' : ∃ l ∈ (⊤ : Subgroup ↥H), ∃ v ∈ N', ⁅l, v⁆ ∉ Z' := by
    obtain ⟨l, hl, v, hv, hne⟩ := hnt
    let v' : ↥H := ⟨v, hNH hv⟩
    refine ⟨⟨l, hl⟩, Subgroup.mem_top _, v', Subgroup.mem_subgroupOf.mpr hv, ?_⟩
    intro hmem
    apply hne
    have hm := Subgroup.mem_subgroupOf.mp hmem
    change ⁅((⟨l, hl⟩ : ↥H) : G), (v' : G)⁆ ∈ X.Z 1 at hm
    rw [commutatorElement_def] at hm
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hm
    simpa [v', commutatorElement_def] using hm
  have hres := two_pow_le_relIndex_of_irreducible (G := ↥H) (V := N') (Z := Z') (L := ⊤)
    (by norm_num : 1 ≤ 2) hquot' hNZ' hsec' hL' hirr' hnt'
  have h16 : (X.Z 1).relIndex N = (Z').relIndex N' :=
    (Subgroup.relIndex_subgroupOf (H := X.Z 1) (K := N) (L := X.L 1) hNH).symm
  rw [h16]
  simpa using hres

private theorem normal_between_centralizes (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N) (hNV : N ≤ X.Vone)
    (hNnorm : X.L 1 ≤ Subgroup.normalizer (N : Set G))
    (hirr : ∀ M : Subgroup G, X.Z 1 ≤ M → M ≤ N →
      X.L 1 ≤ Subgroup.normalizer (M : Set G) → M = X.Z 1 ∨ M = N)
    (hrel8 : (X.Z 1).relIndex N ≤ 8) :
    ⁅N, X.L 1⁆ ≤ X.Z 1 := by
  by_contra h
  have hnt : ∃ l ∈ X.L 1, ∃ v ∈ N, ⁅l, v⁆ ∉ X.Z 1 := by
    by_contra h'
    push Not at h'
    have h'' : ⁅X.L 1, N⁆ ≤ X.Z 1 := Subgroup.commutator_le.mpr h'
    exact h (by simpa [Subgroup.commutator_comm] using h'')
  have h16 := sixteen_le_relIndex_of_nontrivial X hb hc hGT hs hodd h5 hX hn0 hn1
    hZ1N hNV hNnorm hirr hnt
  omega

private theorem normal_between_Y_normal (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) {N : Subgroup G}
    (hNV : N ≤ X.Vone)
    (hNnorm : X.L 1 ≤ Subgroup.normalizer (N : Set G)) :
    X.L 0 ≤ Subgroup.normalizer (((N ⊓ X.Q (-1)) ⊔ X.Z 0 : Subgroup G) : Set G) := by
  let C : Subgroup G := N ⊓ X.Q (-1)
  let D : Subgroup G := X.Q 1 ⊓ X.Q (-1)
  let Y : Subgroup G := C ⊔ X.Z 0
  change X.L 0 ≤ Subgroup.normalizer (Y : Set G)
  have hCY : C ≤ Y := by dsimp [Y]; exact le_sup_left
  have hZY : X.Z 0 ≤ Y := by dsimp [Y]; exact le_sup_right
  have hNQ1 : N ≤ X.Q 1 :=
    hNV.trans (X.Vone_le_Q_one hGT hs hodd h5 hX)
  have hCeq : C = N ⊓ D := by
    dsimp [C, D]
    rw [← inf_assoc, inf_of_le_left hNQ1]
  have hDnorm : X.Gi 0 ≤ Subgroup.normalizer (D : Set G) :=
    Q_one_inf_neg_one_normal X hb hc hGT hs hodd h5 hX
  have hQ1edge0 : X.Q 1 ≤ X.edgeSylow 0 := by
    have h := X.Q_le_edgeSylow_right 1
    simpa [Setup.edgeSylow, show (1 : ℤ) - 1 = 0 by norm_num] using h
  have hVG0 : X.Vone ≤ X.Gi 0 :=
    (X.Vone_le_Q_one hGT hs hodd h5 hX).trans
      (hQ1edge0.trans ((X.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left))
  have hQm1G0 : X.Q (-1) ≤ X.Gi 0 := by
    have h := (X.Q_le_edgeSylow_left (-1)).trans
      ((X.isSylowTwoOf_edgeSylow (-1)).1.trans inf_le_right)
    simpa [show (-1 : ℤ) + 1 = 0 by norm_num] using h
  have hVnegG0 : X.VnegOne ≤ X.Gi 0 :=
    (X.VnegOne_le_Q_neg_one hb hGT hs hodd h5 hX).trans hQm1G0
  have hQ0G0 : X.Q 0 ≤ X.Gi 0 := X.Q_le_Gi 0
  have hQ0L1 : X.Q 0 ≤ X.L 1 :=
    (X.Q_le_edgeSylow_left 0).trans (X.isSylowTwoOf_edgeSylow_L_succ 0).1
  have hVL1 : X.Vone ≤ X.L 1 :=
    (X.Vone_le_Q_one hGT hs hodd h5 hX).trans
      (le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1)) (X.Q_le_Gi 1))
  have hVZ0 : X.Vone ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X hVG0
  have hVnegZ0 : X.VnegOne ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X hVnegG0
  have hQ0Z0 : X.Q 0 ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X hQ0G0
  have hVD : X.Vone ≤ Subgroup.normalizer (D : Set G) := hVG0.trans hDnorm
  have hVN : X.Vone ≤ Subgroup.normalizer (N : Set G) := hVL1.trans hNnorm
  have hVC : X.Vone ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCeq]
    exact (le_inf hVN hVD).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := N) (K := D))
  have hQ0D : X.Q 0 ≤ Subgroup.normalizer (D : Set G) := hQ0G0.trans hDnorm
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (N : Set G) := hQ0L1.trans hNnorm
  have hQ0C : X.Q 0 ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCeq]
    exact (le_inf hQ0N hQ0D).trans
      (Subgroup.inf_normalizer_le_normalizer_inf (H := N) (K := D))
  have hZm1Z0 : X.Z (-1) ≤ X.Z 0 :=
    le_sup_right.trans
      (Z_zero_eq_Z_one_sup_Z_neg_one X hb hc hGT hs hodd h5 hX).ge
  have hVnegComm : ⁅X.VnegOne, C⁆ ≤ X.Z 0 := by
    calc ⁅X.VnegOne, C⁆ ≤ ⁅X.VnegOne, X.Q (-1)⁆ :=
          Subgroup.commutator_mono le_rfl (show C ≤ X.Q (-1) from inf_le_right)
      _ ≤ X.Z (-1) :=
          commutator_VnegOne_Q_neg_one_le X hb hc hGT hs hodd h5 hX
      _ ≤ X.Z 0 := hZm1Z0
  have hCG0 : C ≤ X.Gi 0 := (show C ≤ X.Q (-1) from inf_le_right).trans hQm1G0
  have hCNZ0 : C ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X hCG0
  have hVY : X.Vone ≤ Subgroup.normalizer (Y : Set G) :=
    CFSG.Quasithin.F1.le_normalizer_sup hVC hVZ0
  have hQ0Y : X.Q 0 ≤ Subgroup.normalizer (Y : Set G) :=
    CFSG.Quasithin.F1.le_normalizer_sup hQ0C hQ0Z0
  have hVnegY : X.VnegOne ≤ Subgroup.normalizer (Y : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro v hv y hy
    have hy' : y ∈ C ⊔ X.Z 0 := hy
    obtain ⟨c, hc, z, hz, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hCNZ0).mp hy'
    change MulAut.conj v (c * z) ∈ Y
    rw [map_mul]
    refine Y.mul_mem ?_ ?_
    · have hcomm : ⁅v, c⁆ ∈ X.Z 0 :=
        Subgroup.commutator_le.mp hVnegComm v hv c hc
      have hconj : MulAut.conj v c = ⁅v, c⁆ * c :=
        conj_eq_commutatorElement_mul (g₁ := v) (g₂ := c)
      rw [hconj]
      exact Y.mul_mem (hZY hcomm) (hCY hc)
    · have hvz : MulAut.conj v z ∈ X.Z 0 := by
        have h := (Subgroup.mem_normalizer_iff.mp (hVnegZ0 hv) z).mp hz
        simpa [MulAut.conj_apply] using h
      exact hZY hvz
  have hS : X.edgeSylow 0 = X.Vone ⊔ X.Q 0 :=
    X.edgeSylow_zero.trans
      (S_eq_Vone_sup_Q_zero X hb hc hGT hs hodd h5 hX)
  have hZneg : ¬ X.Z 0 ≤ X.Gi (-3) := X.not_Z_zero_le_Gi_neg_three hb hs h5
  have hGTrev : Even (Nat.card (X.reverse).GT) := by simpa using hGT
  have hrev0 : (X.reverse).n 0 = 1 ∨ (X.reverse).n 0 = 2 := by
    exact Or.inl (by simpa [Setup.n] using hn0)
  have hrev1 : (X.reverse).n 1 = 1 ∨ (X.reverse).n 1 = 2 := by
    have hnn : (X.reverse).n 1 = X.n 1 := by simpa [Setup.n] using X.n_neg_one
    rw [hnn]
    exact Or.inr hn1
  have hrevS := (X.reverse).S_eq_Vone_sup_Q_zero hZneg hc hGTrev hs hodd h5
    (X.reverse_hX hs hodd hX)
  have hSm : X.edgeSylow (-1) = X.VnegOne ⊔ X.Q 0 := by
    simpa [Setup.S, Setup.Vone, Setup.VnegOne, Setup.Q, Setup.edgeSylow, inf_comm] using hrevS
  have hL : X.L 0 = X.edgeSylow 0 ⊔ X.edgeSylow (-1) ⊔ X.Q 0 := by
    rw [sup_comm (X.edgeSylow 0)]
    simpa using L_eq_edgeSylow_sup_Q X 0
  rw [hL]
  refine sup_le ?_ hQ0Y
  refine sup_le ?_ ?_
  · rw [hS]
    exact sup_le hVY hQ0Y
  · rw [hSm]
    exact sup_le hVnegY hQ0Y

private theorem normal_between_Y_commutator (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {N : Subgroup G}
    (hNcommQ : ⁅N ⊓ X.Q (-1), X.Q 0⁆ ≤ X.Z 1)
    (hYnormal : X.L 0 ≤
      Subgroup.normalizer (((N ⊓ X.Q (-1)) ⊔ X.Z 0 : Subgroup G) : Set G)) :
    ⁅(N ⊓ X.Q (-1)) ⊔ X.Z 0, X.Q 0⁆ = ⊥ := by
  let C : Subgroup G := N ⊓ X.Q (-1)
  let Y : Subgroup G := C ⊔ X.Z 0
  change ⁅Y, X.Q 0⁆ = ⊥
  change X.L 0 ≤ Subgroup.normalizer (Y : Set G) at hYnormal
  have hQm1G0 : X.Q (-1) ≤ X.Gi 0 := by
    have h := (X.Q_le_edgeSylow_left (-1)).trans
      ((X.isSylowTwoOf_edgeSylow (-1)).1.trans inf_le_right)
    simpa [show (-1 : ℤ) + 1 = 0 by norm_num] using h
  have hCG0 : C ≤ X.Gi 0 := (show C ≤ X.Q (-1) from inf_le_right).trans hQm1G0
  have hCNZ0 : C ≤ Subgroup.normalizer (X.Z 0 : Set G) :=
    le_normalizer_Z_of_le_Gi X hCG0
  have hcommC : ⁅C, X.Q 0⁆ ≤ X.Z 1 := hNcommQ
  have hcommYZ : ⁅Y, X.Q 0⁆ ≤ X.Z 1 := by
    rw [Subgroup.commutator_le]
    intro y hy q hq
    have hy' : y ∈ C ⊔ X.Z 0 := hy
    obtain ⟨c, hc, z, hz, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_le_normalizer hCNZ0).mp hy'
    rw [commutatorElement_mul_left_eq_conj_mul]
    have hzq : ⁅z, q⁆ = 1 := by
      have hzcent : z ∈ Subgroup.centralizer (X.Q 0 : Set G) :=
        (Subgroup.mem_inf.mp (X.Z_le_center 0 hz)).2
      exact (Subgroup.mem_centralizer_iff_commutator_eq_one'.mp hzcent) q hq
    have hcq : ⁅c, q⁆ ∈ X.Z 1 :=
      Subgroup.commutator_le.mp hcommC c hc q hq
    simpa [hzq] using hcq
  have hlt : X.Z 1 < X.Z 0 :=
    Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0
  have hA_le_Z0 : ⁅Y, X.Q 0⁆ ≤ X.Z 0 := hcommYZ.trans hlt.le
  have hQ0norm : X.L 0 ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    (X.L_le_Gi 0).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hAnorm : X.L 0 ≤
      Subgroup.normalizer ((⁅Y, X.Q 0⁆ : Subgroup G) : Set G) := by
    intro l hl
    let f : G →* G := (MulAut.conj l).toMonoidHom
    have hYl : Subgroup.map f Y = Y := by
      have h := hYnormal hl
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h
      simpa [f, conjSub] using h
    have hQl : Subgroup.map f (X.Q 0) = X.Q 0 := by
      have h := hQ0norm hl
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h
      simpa [f, conjSub] using h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    change Subgroup.map f ⁅Y, X.Q 0⁆ = ⁅Y, X.Q 0⁆
    calc Subgroup.map f ⁅Y, X.Q 0⁆
        = ⁅Subgroup.map f Y, Subgroup.map f (X.Q 0)⁆ :=
          Subgroup.map_commutator (f := f) (H₁ := Y) (H₂ := X.Q 0)
      _ = ⁅Y, X.Q 0⁆ := by rw [hYl, hQl]
  have hA_ne : ⁅Y, X.Q 0⁆ ≠ X.Z 0 := by
    intro hA
    have hZ0leZ1 : X.Z 0 ≤ X.Z 1 := hA ▸ hcommYZ
    exact hlt.ne (le_antisymm hlt.le hZ0leZ1)
  rcases (X.natQuot_Z_zero hb hc hGT hs hodd h5 hX).irred
    ⁅Y, X.Q 0⁆ bot_le hA_le_Z0 hAnorm with h | h
  · exact h
  · exact absurd h hA_ne

private theorem K_le_centralizer_of_normal_between (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {N : Subgroup G}
    (hNcomm : ⁅N, X.L 1⁆ ≤ X.Z 1) :
    X.K ≤ Subgroup.centralizer (N : Set G) := by
  classical
  have hK1 : X.K = X.Ki 1 := K_eq_Ki_one X hb hc hGT hs hodd h5 hX hn0
  have hKL1 : X.K ≤ X.L 1 := hK1.le.trans inf_le_right
  have hZ1center : X.Z 1 = centerOf (X.L 1) :=
    X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro n hn
  have hkL1 : k ∈ X.L 1 := hKL1 hk
  have hz1 : ⁅k, n⁆ ∈ X.Z 1 := by
    have hmem : ⁅k, n⁆ ∈ ⁅X.L 1, N⁆ := Subgroup.commutator_mem_commutator hkL1 hn
    rw [Subgroup.commutator_comm (H₁ := X.L 1) (H₂ := N)] at hmem
    exact hNcomm hmem
  have hz0 : ⁅k, n⁆ ∈ X.Z 0 :=
    (Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le hz1
  have hz2 : ⁅k, n⁆ ^ 2 = 1 :=
    Z_zero_sq X hb hc hGT hs hodd h5 hX hn0 hz0
  have hkz : k * ⁅k, n⁆ * k⁻¹ = ⁅k, n⁆ := by
    have hzC : ⁅k, n⁆ ∈ Subgroup.centralizer (X.L 1 : Set G) := by
      have h : ⁅k, n⁆ ∈ centerOf (X.L 1) := by rwa [← hZ1center]
      exact (Subgroup.mem_inf.mp h).2
    have hcomm : k * ⁅k, n⁆ = ⁅k, n⁆ * k :=
      Subgroup.mem_centralizer_iff.mp hzC k hkL1
    calc k * ⁅k, n⁆ * k⁻¹ = (⁅k, n⁆ * k) * k⁻¹ := by rw [hcomm]
      _ = ⁅k, n⁆ := by group
  have h1 : k * n * k⁻¹ = ⁅k, n⁆ * n := by
    rw [commutatorElement_def]
    group
  have h3 : k ^ 2 * n * (k ^ 2)⁻¹ = n := by
    have h4 : k * (⁅k, n⁆ * n) * k⁻¹ = n := by
      calc k * (⁅k, n⁆ * n) * k⁻¹
          = (k * ⁅k, n⁆ * k⁻¹) * (k * n * k⁻¹) := by group
        _ = ⁅k, n⁆ * (⁅k, n⁆ * n) := by rw [hkz, h1]
        _ = n := by rw [← mul_assoc, ← pow_two, hz2, one_mul]
    calc k ^ 2 * n * (k ^ 2)⁻¹ = k * (k * n * k⁻¹) * k⁻¹ := by
          rw [pow_two]
          group
      _ = k * (⁅k, n⁆ * n) * k⁻¹ := by rw [h1]
      _ = n := h4
  have hkodd : Odd (orderOf k) := by
    have h := orderOf_dvd_natCard (⟨k, hk⟩ : ↥X.K)
    rw [Subgroup.orderOf_mk] at h
    exact X.odd_card_K.of_dvd_nat h
  exact ((CFSG.Wreathed.ConfinedOddCore.commute_of_sq_commute hkodd
    (show Commute (k ^ 2) n from mul_inv_eq_iff_eq_mul.mp h3)).eq).symm

private theorem false_of_normal_between_Q_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N)
    (hNQ0 : N ≤ X.Q 0)
    (hNQm : N ⊓ X.Q (-1) = X.Z 1)
    (hrel2 : (X.Z 1).relIndex N = 2)
    (hNcomm : ⁅N, X.L 1⁆ ≤ X.Z 1) : False := by
  have hKcent : X.K ≤ Subgroup.centralizer (N : Set G) :=
    K_le_centralizer_of_normal_between X hb hc hGT hs hodd h5 hX hn0 hNcomm
  have hNne : N ≠ X.Z 1 := by
    intro h
    have h1 : (X.Z 1).relIndex N = 1 := by
      rw [h]
      exact Subgroup.relIndex_self (H := X.Z 1)
    omega
  have hnot : ¬ N ≤ X.Z 1 := fun h => hNne (le_antisymm h hZ1N)
  obtain ⟨n, hnN, hnZ1⟩ := Set.not_subset.mp hnot
  have hnQm : n ∉ X.Q (-1) := by
    intro h
    have hmem : n ∈ N ⊓ X.Q (-1) := Subgroup.mem_inf.mpr ⟨hnN, h⟩
    rw [hNQm] at hmem
    exact hnZ1 hmem
  have hQ0Gm : X.Q 0 ≤ X.Gi (-1) := by
    have h := (X.Q_le_Gi_adj 0).trans inf_le_left
    rwa [show (0 : ℤ) - 1 = -1 by norm_num] at h
  have hQ0S : X.Q 0 ≤ X.edgeSylow (-1) := by
    have h := X.edgeSylow_right_eq 0
    rw [show (0 : ℤ) - 1 = -1 by norm_num] at h
    rw [h]
    exact X.Q_le_edgeSylow_right 0
  have hnS : n ∈ X.edgeSylow (-1) := hQ0S (hNQ0 hnN)
  have hrelS : (X.Q (-1)).relIndex (X.edgeSylow (-1)) = 4 := by
    rw [X.relIndex_Q_edgeSylow (-1), X.n_neg_one, hn1]
    norm_num
  have hrelQN : (X.Q (-1)).relIndex N = 2 := by
    rw [← Subgroup.inf_relIndex_right (H := X.Q (-1)) (K := N),
      inf_comm (X.Q (-1)) N, hNQm, hrel2]
  have hQnorm : N ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    (hNQ0.trans hQ0Gm).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (G := G) 2 (X.Gi (-1)))
  have hrelSup : (X.Q (-1)).relIndex (N ⊔ X.Q (-1)) = 2 := by
    rw [CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hQnorm, hrelQN]
  have hQmS : X.Q (-1) ≤ X.edgeSylow (-1) := X.Q_le_edgeSylow_left (-1)
  have hNQleS : N ⊔ X.Q (-1) ≤ X.edgeSylow (-1) := sup_le (hNQ0.trans hQ0S) hQmS
  have hnotle : ¬ X.edgeSylow (-1) ≤ N ⊔ X.Q (-1) := by
    intro hle
    have heq : X.edgeSylow (-1) = N ⊔ X.Q (-1) := le_antisymm hle hNQleS
    have h2 : (X.Q (-1)).relIndex (X.edgeSylow (-1)) =
        (X.Q (-1)).relIndex (N ⊔ X.Q (-1)) := by rw [heq]
    rw [hrelS, hrelSup] at h2
    norm_num at h2
  obtain ⟨y, hyS, hyNQ⟩ := Set.not_subset.mp hnotle
  have hyQm : y ∉ X.Q (-1) := fun h => hyNQ (Subgroup.mem_sup_right h)
  obtain ⟨k, hkK, hkconj⟩ := X.exists_conj_mem_Q_left (-1) hnS hyS hnQm hyQm
  have hkcent : k ∈ Subgroup.centralizer (N : Set G) := hKcent hkK.1
  have hnk : n * k = k * n := Subgroup.mem_centralizer_iff.mp hkcent n hnN
  have hkn : k * n * k⁻¹ = n := by
    calc k * n * k⁻¹ = (n * k) * k⁻¹ := by rw [hnk]
      _ = n := by group
  rw [hkn] at hkconj
  have hyNQ' : y ∈ N ⊔ X.Q (-1) := by
    have hy : y = (n * y⁻¹)⁻¹ * n := by group
    rw [hy]
    exact (N ⊔ X.Q (-1)).mul_mem
      ((N ⊔ X.Q (-1)).inv_mem (Subgroup.mem_sup_right hkconj))
      (Subgroup.mem_sup_left hnN)
  exact hyNQ hyNQ'

private theorem normal_between_relIndex_le_eight (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N) (hNV : N ≤ X.Vone)
    (hNQm : N ⊓ X.Q (-1) = X.Z 1) :
    (X.Z 1).relIndex N ≤ 8 := by
  let A0 : Subgroup G := N ⊓ X.Q 0
  let C : Subgroup G := X.Q (-1) ⊓ X.Q 1
  let A' : Subgroup G := X.Q 0 ⊓ X.Q 1
  have hVQ1 : X.Vone ≤ X.Q 1 :=
    X.Vone_le_Q_one hGT hs hodd h5 hX
  have hQ1S : X.Q 1 ≤ X.S := by
    have h := X.Q_le_edgeSylow (0 : ℤ)
    rw [X.edgeSylow_zero] at h
    simpa using h
  have hSG0 : X.S ≤ X.Gi 0 :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi 0 ⊓ X.Gi 1)).trans inf_le_left
  have hQ0G0 : X.Q 0 ≤ X.Gi 0 := X.Q_le_Gi 0
  have hQ0S : X.Q 0 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow_left 0
  have hNQ1 : N ≤ X.Q 1 := hNV.trans hVQ1
  have hNG0 : N ≤ X.Gi 0 := hNQ1.trans (hQ1S.trans hSG0)
  have hZ1G0 : X.Z 1 ≤ X.Gi 0 := (X.Z_le_Q 1).trans (hQ1S.trans hSG0)
  haveI hSfin : Finite ↥X.S := finite_of_le_stabilizer X.hyp hSG0
  haveI hQ0fin : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp hQ0G0
  haveI hCfin : Finite ↥C :=
    finite_of_le_stabilizer X.hyp (H := C) (by
      calc C ≤ X.Q 1 := inf_le_right
        _ ≤ X.S := hQ1S
        _ ≤ X.Gi 0 := hSG0)
  haveI hZ1fin : Finite ↥(X.Z 1) := finite_of_le_stabilizer X.hyp hZ1G0
  haveI hA'fin : Finite ↥A' :=
    finite_of_le_stabilizer X.hyp (H := A') (by
      calc A' ≤ X.Q 0 := inf_le_left
        _ ≤ X.Gi 0 := hQ0G0)
  have hQ0Srel : (X.Q 0).relIndex X.S = 2 := by
    rw [← X.edgeSylow_zero, X.relIndex_Q_edgeSylow 0, hn0]
    norm_num
  have hcardS : Nat.card X.S = 2 * Nat.card ↥(X.Q 0) := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 0) (K := X.S)
    rw [hQ0Srel, inf_of_le_left hQ0S] at h
    exact h.symm
  have hNnormQ0 : N ≤ Subgroup.normalizer (X.Q 0 : Set G) :=
    hNG0.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 0))
  have hcommNQ0 : ∀ b ∈ N, ∀ n ∈ X.Q 0, b * n * b⁻¹ ∈ X.Q 0 := by
    intro b hb n hn
    exact ((Subgroup.mem_normalizer_iff.mp (hNnormQ0 hb)) n).mp hn
  have hprodNQ0 :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
      N (X.Q 0) hcommNQ0
  have hNS : N ⊔ X.Q 0 ≤ X.S :=
    sup_le (hNV.trans (hVQ1.trans hQ1S)) hQ0S
  have hcardNS : Nat.card ↥(N ⊔ X.Q 0) ≤ Nat.card X.S := Subgroup.card_le_of_le hNS
  have h1 : Nat.card ↥N * Nat.card ↥(X.Q 0) ≤
      2 * Nat.card ↥(X.Q 0) * Nat.card ↥(N ⊓ X.Q 0) := by
    calc Nat.card ↥N * Nat.card ↥(X.Q 0)
        = Nat.card ↥(N ⊔ X.Q 0) * Nat.card ↥(N ⊓ X.Q 0) := hprodNQ0.symm
      _ ≤ Nat.card X.S * Nat.card ↥(N ⊓ X.Q 0) := Nat.mul_le_mul_right _ hcardNS
      _ = (2 * Nat.card ↥(X.Q 0)) * Nat.card ↥(N ⊓ X.Q 0) := by rw [hcardS]
  have hQ0pos : 0 < Nat.card ↥(X.Q 0) := Nat.card_pos
  have hNle : Nat.card ↥N ≤ 2 * Nat.card ↥(N ⊓ X.Q 0) := by
    have h1' : Nat.card ↥(X.Q 0) * Nat.card ↥N ≤
        Nat.card ↥(X.Q 0) * (2 * Nat.card ↥(N ⊓ X.Q 0)) := by
      calc Nat.card ↥(X.Q 0) * Nat.card ↥N
          = Nat.card ↥N * Nat.card ↥(X.Q 0) := Nat.mul_comm _ _
        _ ≤ (2 * Nat.card ↥(X.Q 0)) * Nat.card ↥(N ⊓ X.Q 0) := h1
        _ = Nat.card ↥(X.Q 0) * (2 * Nat.card ↥(N ⊓ X.Q 0)) := by ring
    exact Nat.le_of_mul_le_mul_left h1' hQ0pos
  have hGi0normC : X.Gi 0 ≤ Subgroup.normalizer (C : Set G) := by
    have h := Q_one_inf_neg_one_normal X hb hc hGT hs hodd h5 hX
    simpa [C, inf_comm] using h
  have hCQ0 : C ≤ X.Q 0 := (inf_comm (X.Q (-1)) (X.Q 1)).le.trans
    (le_sup_right.trans (Q_zero_eq_sup X hb hc hGT hs hodd h5 hX).ge)
  have hCA' : C ≤ A' := by
    dsimp [A', C]
    exact le_inf hCQ0 inf_le_right
  have hrelCA' : C.relIndex A' = 4 := by
    have h := (X.Q_quot_of_normal_general hc hs (by omega)).2.2.1
    rw [hn1] at h
    norm_num at h
    simpa [C, A'] using h
  have hcardA' : Nat.card ↥A' = 4 * Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := A')
    rw [hrelCA', inf_of_le_left hCA'] at h
    exact h.symm
  have hA0normC : A0 ≤ Subgroup.normalizer (C : Set G) :=
    (inf_le_right.trans hQ0G0).trans hGi0normC
  have hcommA0C : ∀ b ∈ A0, ∀ n ∈ C, b * n * b⁻¹ ∈ C := by
    intro b hb n hn
    exact ((Subgroup.mem_normalizer_iff.mp (hA0normC hb)) n).mp hn
  have hprodA0C :=
    CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
      A0 C hcommA0C
  have hACinf : A0 ⊓ C = X.Z 1 := by
    have h1 : A0 ⊓ C = N ⊓ C := by
      dsimp [A0]
      rw [inf_assoc, inf_eq_right.mpr hCQ0]
    calc A0 ⊓ C = N ⊓ C := h1
      _ = (N ⊓ X.Q (-1)) ⊓ X.Q 1 := by dsimp [C]; rw [inf_assoc]
      _ = X.Z 1 ⊓ X.Q 1 := by rw [hNQm]
      _ = X.Z 1 := inf_of_le_left (X.Z_le_Q 1)
  have hACA' : A0 ⊔ C ≤ A' :=
    sup_le (le_inf inf_le_right (inf_le_left.trans hNQ1)) hCA'
  have hcardA0sup : Nat.card ↥(A0 ⊔ C) ≤ Nat.card ↥A' := Subgroup.card_le_of_le hACA'
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hA0le : Nat.card ↥A0 ≤ 4 * Nat.card ↥(X.Z 1) := by
    have h1 : Nat.card ↥A0 * Nat.card ↥C ≤ 4 * Nat.card ↥(X.Z 1) * Nat.card ↥C := by
      calc Nat.card ↥A0 * Nat.card ↥C
          = Nat.card ↥(A0 ⊔ C) * Nat.card ↥(A0 ⊓ C) := hprodA0C.symm
        _ = Nat.card ↥(A0 ⊔ C) * Nat.card ↥(X.Z 1) := by rw [hACinf]
        _ ≤ Nat.card ↥A' * Nat.card ↥(X.Z 1) := Nat.mul_le_mul_right _ hcardA0sup
        _ = (4 * Nat.card ↥C) * Nat.card ↥(X.Z 1) := by rw [hcardA']
        _ = 4 * Nat.card ↥(X.Z 1) * Nat.card ↥C := by ring
    exact Nat.le_of_mul_le_mul_right h1 hCpos
  have hZ1pos : 0 < Nat.card ↥(X.Z 1) := Nat.card_pos
  have hfinal : (X.Z 1).relIndex N * Nat.card ↥(X.Z 1) ≤ 8 * Nat.card ↥(X.Z 1) := by
    calc (X.Z 1).relIndex N * Nat.card ↥(X.Z 1)
        = Nat.card ↥N := by
          have h := Subgroup.relIndex_mul_card (H := X.Z 1) (K := N)
          rwa [inf_of_le_left hZ1N] at h
      _ ≤ 2 * Nat.card ↥(N ⊓ X.Q 0) := hNle
      _ ≤ 2 * (4 * Nat.card ↥(X.Z 1)) := Nat.mul_le_mul_left 2 hA0le
      _ = 8 * Nat.card ↥(X.Z 1) := by ring
  exact Nat.le_of_mul_le_mul_right hfinal hZ1pos

private theorem normal_between_relIndex_eq_two (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N) (hNV : N ≤ X.Vone) (hZ1Nlt : X.Z 1 < N)
    (hirrN : ∀ M : Subgroup G, X.Z 1 ≤ M → M ≤ N →
      X.L 1 ≤ Subgroup.normalizer (M : Set G) → M = X.Z 1 ∨ M = N)
    (hNcomm : ⁅N, X.L 1⁆ ≤ X.Z 1) :
    (X.Z 1).relIndex N = 2 := by
  have hVQ1 : X.Vone ≤ X.Q 1 :=
    X.Vone_le_Q_one hGT hs hodd h5 hX
  have hQ1L1 : X.Q 1 ≤ X.L 1 :=
    le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1))
      (CFSG.LieType.BorelTits.pCoreOf_le 2 (X.Gi 1))
  have hex : ∃ x ∈ N, x ∉ X.Z 1 := by
    by_contra h
    have hle : N ≤ X.Z 1 := by
      intro x hx
      by_contra hxZ
      exact h ⟨x, hx, hxZ⟩
    exact ne_of_lt hZ1Nlt (le_antisymm hle hZ1N).symm
  obtain ⟨n, hnN, hnZ⟩ := hex
  have hnV : n ∈ X.Vone := hNV hnN
  have hnQ1 : n ∈ X.Q 1 := hVQ1 hnV
  have hnL1 : n ∈ X.L 1 := hQ1L1 hnQ1
  have hZ1cent : X.Z 1 ≤ Subgroup.centralizer (X.L 1 : Set G) := by
    rw [X.Z_one_eq_centerOf_L_one hb hc hGT hs hodd h5 hX]
    exact inf_le_right
  have hn2 : n * n ∈ X.Z 1 := by
    have h := (isElemSec_Z_one_Vone X hb hc hGT hs hodd h5 hX hn0).2.2 n hnV
    simpa [pow_two] using h
  have hn2inv : n⁻¹ * n⁻¹ ∈ X.Z 1 := by
    have h := (X.Z 1).inv_mem hn2
    simpa [mul_inv_rev] using h
  let T : Subgroup G :=
    { carrier := {x : G | x ∈ X.Z 1 ∨ ∃ z ∈ X.Z 1, z * n = x}
      one_mem' := Or.inl (X.Z 1).one_mem
      mul_mem' := by
        rintro x y (hx | ⟨a, ha, rfl⟩) (hy | ⟨b, hb, rfl⟩)
        · exact Or.inl ((X.Z 1).mul_mem hx hy)
        · exact Or.inr ⟨x * b, (X.Z 1).mul_mem hx hb, mul_assoc x b n⟩
        · have hny : n * y = y * n :=
            Subgroup.mem_centralizer_iff.mp (hZ1cent hy) n hnL1
          have heq : (a * n) * y = (a * y) * n := by
            calc (a * n) * y = a * (n * y) := by group
              _ = a * (y * n) := by rw [hny]
              _ = (a * y) * n := by group
          exact Or.inr ⟨a * y, (X.Z 1).mul_mem ha hy, heq.symm⟩
        · have hnb : n * b = b * n :=
            Subgroup.mem_centralizer_iff.mp (hZ1cent hb) n hnL1
          refine Or.inl ?_
          have heq : (a * n) * (b * n) = (a * b) * (n * n) := by
            calc (a * n) * (b * n) = a * (n * b) * n := by group
              _ = a * (b * n) * n := by rw [hnb]
              _ = (a * b) * (n * n) := by group
          rw [heq]
          exact (X.Z 1).mul_mem ((X.Z 1).mul_mem ha hb) hn2
      inv_mem' := by
        rintro x (hx | ⟨a, ha, rfl⟩)
        · exact Or.inl ((X.Z 1).inv_mem hx)
        · refine Or.inr ⟨(n⁻¹ * n⁻¹) * a⁻¹, (X.Z 1).mul_mem hn2inv ((X.Z 1).inv_mem ha), ?_⟩
          have hcomm : a⁻¹ * n = n * a⁻¹ :=
            (Subgroup.mem_centralizer_iff.mp (hZ1cent ((X.Z 1).inv_mem ha)) n hnL1).symm
          rw [mul_inv_rev]
          calc (n⁻¹ * n⁻¹) * a⁻¹ * n = (n⁻¹ * n⁻¹) * (a⁻¹ * n) := by group
            _ = (n⁻¹ * n⁻¹) * (n * a⁻¹) := by rw [hcomm]
            _ = n⁻¹ * a⁻¹ := by group }
  have hTmem : ∀ b : G, b ∈ T ↔ b ∈ X.Z 1 ∨ ∃ z ∈ X.Z 1, z * n = b := by
    intro b
    dsimp [T]
    rfl
  have hMT : (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) ≤ T :=
    sup_le (fun x hx => (hTmem x).mpr (Or.inl hx))
      (Subgroup.zpowers_le.mpr ((hTmem n).mpr (Or.inr ⟨1, (X.Z 1).one_mem, one_mul n⟩)))
  have hconjZ : ∀ (g : G), g ∈ X.L 1 → ∀ z ∈ X.Z 1, g * z * g⁻¹ = z := by
    intro g hg z hz
    have h := Subgroup.mem_centralizer_iff.mp (hZ1cent hz) g hg
    calc g * z * g⁻¹ = z * g * g⁻¹ := by rw [h]
      _ = z := by group
  have hforward : ∀ (g : G), g ∈ X.L 1 → ∀ m : G,
      m ∈ (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) →
      g * m * g⁻¹ ∈ (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) := by
    intro g hg m hm
    rcases (hTmem m).mp (hMT hm) with hmZ | ⟨z, hz, rfl⟩
    · rw [hconjZ g hg m hmZ]
      exact Subgroup.mem_sup_left hmZ
    · have hgl : ⁅n, g⁆ ∈ X.Z 1 := hNcomm (Subgroup.commutator_mem_commutator hnN hg)
      have hgl' : ⁅n, g⁆⁻¹ ∈ X.Z 1 := (X.Z 1).inv_mem hgl
      have hgln : g * n * g⁻¹ = ⁅n, g⁆⁻¹ * n := by
        rw [commutatorElement_def]
        group
      have hgn : g * n * g⁻¹ ∈ (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) := by
        rw [hgln]
        exact Subgroup.mul_mem_sup hgl' (Subgroup.mem_zpowers n)
      have heq : g * (z * n) * g⁻¹ = z * (g * n * g⁻¹) := by
        calc g * (z * n) * g⁻¹ = (g * z * g⁻¹) * (g * n * g⁻¹) := by group
          _ = z * (g * n * g⁻¹) := by rw [hconjZ g hg z hz]
      rw [heq]
      exact (X.Z 1 ⊔ Subgroup.zpowers n).mul_mem (Subgroup.mem_sup_left hz) hgn
  have hnormM : X.L 1 ≤ Subgroup.normalizer (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro m
    exact ⟨fun hm => hforward g hg m hm, fun hm => by
      have h := hforward g⁻¹ ((X.L 1).inv_mem hg) (g * m * g⁻¹) hm
      rwa [show g⁻¹ * (g * m * g⁻¹) * (g⁻¹)⁻¹ = m from by group] at h⟩
  have hMn : (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) = N := by
    rcases hirrN (X.Z 1 ⊔ Subgroup.zpowers n) le_sup_left
        (sup_le hZ1N (Subgroup.zpowers_le.mpr hnN)) hnormM with h | h
    · exfalso
      have hm : n ∈ (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers n)
      rw [h] at hm
      exact hnZ hm
    · exact h
  have hdecomp : ∀ b ∈ N, b ∈ X.Z 1 ∨ ∃ z ∈ X.Z 1, z * n = b := by
    intro b hb
    have hbM : b ∈ (X.Z 1 ⊔ Subgroup.zpowers n : Subgroup G) := by
      rw [hMn]
      exact hb
    exact (hTmem b).mp (hMT hbM)
  have hall : ∀ b ∈ N, n * b ∈ X.Z 1 ∨ b ∈ X.Z 1 := by
    intro b hb
    rcases hdecomp b hb with hbZ | ⟨z, hz, rfl⟩
    · exact Or.inr hbZ
    · refine Or.inl ?_
      have hnb : n * z = z * n := Subgroup.mem_centralizer_iff.mp (hZ1cent hz) n hnL1
      have heq : n * (z * n) = z * (n * n) := by
        calc n * (z * n) = (n * z) * n := by group
          _ = (z * n) * n := by rw [hnb]
          _ = z * (n * n) := by group
      rw [heq]
      exact (X.Z 1).mul_mem hz hn2
  exact (Subgroup.relIndex_eq_two_iff_exists_notMem_and').mpr ⟨n, hnN, hnZ, hall⟩

private theorem S_eq_sup_zpowers_of_relIndex_two {s : G}
    (hQ0S : X.Q 0 ≤ X.S) (hrel : (X.Q 0).relIndex X.S = 2)
    (hsS : s ∈ X.S) (hsQ : s ∉ X.Q 0) :
    X.S = X.Q 0 ⊔ Subgroup.zpowers s := by
  obtain ⟨a, haS, haQ, hxor⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hrel
  have hsa : s * a ∈ X.Q 0 := by
    rcases hxor s hsS with h | h
    · exact h
    · exact absurd h hsQ
  have haH : a ∈ X.Q 0 ⊔ Subgroup.zpowers s := by
    have h1 : s⁻¹ ∈ Subgroup.zpowers s :=
      Subgroup.inv_mem _ (Subgroup.mem_zpowers s)
    have h2 : s⁻¹ * (s * a) = a := by group
    rw [← h2]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hsa)
  refine le_antisymm ?_ (sup_le hQ0S (Subgroup.zpowers_le.mpr hsS))
  intro b hbS
  by_cases hbQ : b ∈ X.Q 0
  · exact Subgroup.mem_sup_left hbQ
  · have hba : b * a ∈ X.Q 0 := by
      rcases hxor b hbS with h | h
      · exact h
      · exact absurd h hbQ
    have hb : b = (b * a) * a⁻¹ := by group
    rw [hb]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hba) (Subgroup.inv_mem _ haH)

private theorem mem_Z_zero_of_mem_Q_zero_of_mem_centralizer_S {y : G}
    (hyQ0 : y ∈ X.Q 0) (hyc : y ∈ Subgroup.centralizer (X.S : Set G)) :
    y ∈ X.Z 0 := by
  have hS_syl : IsSylowTwoOf X.S (X.Gi 0) := by
    rw [← X.edgeSylow_zero]
    exact isSylowTwoOf_of_edgeStab X.hyp (X.adj 0) (X.isSylowTwoOf_edgeSylow 0)
  have hyS : y ∈ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow_left 0 hyQ0
  have hycent : y ∈ centerOf X.S := Subgroup.mem_inf.mpr ⟨hyS, hyc⟩
  unfold Setup.Z
  exact Subgroup.mem_iSup_of_mem X.S
    (Subgroup.mem_iSup_of_mem hS_syl (Subgroup.mem_inf.mpr ⟨hycent, hyQ0⟩))

private theorem mem_centralizer_sup_zpowers_of_fixed {Q : Subgroup G} {s u : G}
    (hQcent : Q ≤ Subgroup.centralizer ({u} : Set G)) (hfix : s * u * s⁻¹ = u) :
    u ∈ Subgroup.centralizer (Q ⊔ Subgroup.zpowers s : Subgroup G) := by
  have hs : s ∈ Subgroup.centralizer ({u} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [hfix]
  have hle : Q ⊔ Subgroup.zpowers s ≤ Subgroup.centralizer ({u} : Set G) :=
    sup_le hQcent (Subgroup.zpowers_le.mpr hs)
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle ha)

private theorem Q_zero_le_centralizer_singleton {u : G} (hu : u ∈ X.Z 0) :
    X.Q 0 ≤ Subgroup.centralizer ({u} : Set G) := by
  intro qq hq
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst h
  exact (Subgroup.mem_centralizer_iff.mp
    (Subgroup.mem_inf.mp (X.Z_le_center 0 hu)).2 qq hq).symm

open scoped IsMulCommutative in
private theorem normal_between_inf_Q_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N) (hNV : N ≤ X.Vone)
    (hNZ0 : N ⊓ X.Z 0 = X.Z 1)
    (hYnormal : X.L 0 ≤ Subgroup.normalizer (((N ⊓ X.Q (-1)) ⊔ X.Z 0 : Subgroup G) : Set G))
    (hYcomm : ⁅(N ⊓ X.Q (-1)) ⊔ X.Z 0, X.Q 0⁆ = ⊥) :
    N ⊓ X.Q (-1) = X.Z 1 := by
  by_contra hgoal
  let P : Subgroup G := N ⊓ X.Q (-1)
  let Y : Subgroup G := P ⊔ X.Z 0
  change P ≠ X.Z 1 at hgoal
  have hZ1Qneg : X.Z 1 ≤ X.Q (-1) :=
    (Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le.trans
      (Z_zero_le_Q_neg_one X hb hGT hs hodd h5 hX)
  have hZ1P : X.Z 1 ≤ P := le_inf hZ1N hZ1Qneg
  have hZ0Y : X.Z 0 ≤ Y := le_sup_right
  have hPY : P ≤ Y := le_sup_left
  have hYQ0 : Y ≤ X.Q 0 := by
    have hVQ1 : X.Vone ≤ X.Q 1 :=
      X.Vone_le_Q_one hGT hs hodd h5 hX
    have hPC : P ≤ X.Q 1 ⊓ X.Q (-1) :=
      le_inf (inf_le_left.trans (hNV.trans hVQ1)) inf_le_right
    have hCQ0 : X.Q 1 ⊓ X.Q (-1) ≤ X.Q 0 :=
      le_sup_right.trans (Q_zero_eq_sup X hb hc hGT hs hodd h5 hX).ge
    exact sup_le (hPC.trans hCQ0) (X.Z_le_Q 0)
  have hQ0leCentY : X.Q 0 ≤ Subgroup.centralizer (Y : Set G) := by
    have h : ⁅X.Q 0, Y⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact hYcomm
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hYab : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp (hQ0leCentY (hYQ0 ha)) b hb).symm
  haveI hYcommGroup : IsMulCommutative ↥Y :=
    IsMulCommutative.of_comm (fun a b => Subtype.ext (hYab (a : G) a.2 (b : G) b.2))
  haveI hYfin : Finite ↥Y :=
    finite_of_le_stabilizer X.hyp (H := Y) (hYQ0.trans (X.Q_le_Gi 0))
  have hYne : Y ≠ X.Z 0 := by
    intro hYeq
    apply hgoal
    have hPleNZ0 : P ≤ N ⊓ X.Z 0 := le_inf inf_le_left (hYeq ▸ hPY)
    have hPleZ1 : P ≤ X.Z 1 := hNZ0 ▸ hPleNZ0
    exact le_antisymm hPleZ1 hZ1P
  have hrelQ0S : (X.Q 0).relIndex X.S = 2 := relIndex_Q_zero_S_eq_two X hn0
  have hQ0S : X.Q 0 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow_left 0
  obtain ⟨s, hsS, hsQ, hxor⟩ :=
    Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp hrelQ0S
  have hSsup : X.S = X.Q 0 ⊔ Subgroup.zpowers s :=
    S_eq_sup_zpowers_of_relIndex_two X hQ0S hrelQ0S hsS hsQ
  have hSleL0 : X.S ≤ X.L 0 := by
    rw [← X.edgeSylow_zero]
    exact (X.isSylowTwoOf_edgeSylow_L 0).1
  have hsL0 : s ∈ X.L 0 := hSleL0 hsS
  have hs2Q : s ^ 2 ∈ X.Q 0 :=
    X.sq_mem_Q_of_relIndex (S := X.S) (j := 0) hSleL0 (by
      rw [hrelQ0S, hn0]; norm_num) s hsS
  have hsnormY : s ∈ Subgroup.normalizer (Y : Set G) := hYnormal hsL0
  let φ : MulAut ↥Y := Subgroup.normalizerMonoidHom Y ⟨s, hsnormY⟩
  have hφapply : ∀ y : ↥Y, ((φ y : ↥Y) : G) = s * (y : G) * s⁻¹ :=
    fun y => rfl
  have hs2centY : s ^ 2 ∈ Subgroup.centralizer (Y : Set G) := hQ0leCentY hs2Q
  have hφ2 : ∀ y : ↥Y, φ (φ y) = y := by
    intro y
    apply Subtype.ext
    rw [hφapply, hφapply]
    have hc := Subgroup.mem_centralizer_iff.mp hs2centY (y : G) y.2
    calc s * (s * (y : G) * s⁻¹) * s⁻¹
        = (s * s) * (y : G) * (s⁻¹ * s⁻¹) := by group
      _ = s ^ 2 * (y : G) * (s ^ 2)⁻¹ := by
          rw [show s * s = s ^ 2 by rw [pow_two],
            show s⁻¹ * s⁻¹ = (s ^ 2)⁻¹ by rw [pow_two, mul_inv_rev]]
      _ = (y : G) := by
          rw [show s ^ 2 * (y : G) = (y : G) * s ^ 2 from hc.symm]
          group
  let N₀ : Subgroup ↥Y := (X.Z 0).subgroupOf Y
  have hφmemN : ∀ y : ↥Y, y ∈ N₀ → φ y ∈ N₀ := by
    intro y hy
    have hyZ : (y : G) ∈ X.Z 0 := Subgroup.mem_subgroupOf.mp hy
    have hsnormZ0 : s ∈ Subgroup.normalizer (X.Z 0 : Set G) :=
      le_normalizer_Z_of_le_Gi X (X.L_le_Gi 0) hsL0
    have hconjZ : s * (y : G) * s⁻¹ ∈ X.Z 0 :=
      (Subgroup.mem_normalizer_iff.mp hsnormZ0 (y : G)).mp hyZ
    rw [Subgroup.mem_subgroupOf, hφapply]
    exact hconjZ
  have hφNle : N₀.map (φ : ↥Y →* ↥Y) ≤ N₀ := by
    rintro z ⟨y, hy, rfl⟩
    exact hφmemN y hy
  haveI hN₀fin : Finite ↥N₀ := Subtype.finite
  have hφNmap : N₀.map (φ : ↥Y →* ↥Y) = N₀ := by
    refine Subgroup.eq_of_le_of_card_ge hφNle ?_
    have hcard : Nat.card ↥(N₀.map (φ : ↥Y →* ↥Y)) = Nat.card ↥N₀ :=
      Subgroup.card_map_of_injective (K := N₀) (f := (φ : ↥Y →* ↥Y)) φ.injective
    rw [hcard]
  haveI hN₀normal : N₀.Normal := Subgroup.normal_of_isMulCommutative N₀
  let ψ : (↥Y ⧸ N₀) ≃* (↥Y ⧸ N₀) := QuotientGroup.congr N₀ N₀ φ hφNmap
  have hψapply : ∀ y : ↥Y, ψ (QuotientGroup.mk y) = QuotientGroup.mk (φ y) :=
    fun y => QuotientGroup.congr_mk N₀ N₀ φ hφNmap y
  have hψ2 : Function.Involutive ψ := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro y
    rw [hψapply, hψapply, hφ2 y]
  have hZ1card : Nat.card ↥(X.Z 1) = 2 :=
    card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0
  have hZ1Y : X.Z 1 ≤ Y := hZ1P.trans hPY
  have hZ1subcard : Nat.card ↥((X.Z 1).subgroupOf Y) = 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ1Y).toEquiv]
    exact hZ1card
  have hZ1neBot : X.Z 1 ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(X.Z 1) = 1 := by rw [hbot, Subgroup.card_bot]
    omega
  have hN₀neTop : N₀ ≠ ⊤ := by
    intro htop
    apply hYne
    refine le_antisymm ?_ hZ0Y
    intro y hy
    have hyN : (⟨y, hy⟩ : ↥Y) ∈ N₀ := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hyN
  have hY2 : IsPGroup 2 ↥Y :=
    (CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 0)).to_le hYQ0
  have hQ2 : IsPGroup 2 (↥Y ⧸ N₀) := hY2.to_quotient N₀
  have hQnontriv : Nontrivial (↥Y ⧸ N₀) := QuotientGroup.nontrivial_iff.mpr hN₀neTop
  have heven : Even (Nat.card (↥Y ⧸ N₀)) := by
    rcases hQ2.card_eq_or_dvd with h | h
    · exfalso
      have hsub : Subsingleton (↥Y ⧸ N₀) := (Nat.card_eq_one_iff_unique.mp h).1
      exact (not_subsingleton_iff_nontrivial.mpr hQnontriv) hsub
    · exact even_iff_two_dvd.mpr h
  have hex : ∃ q : (↥Y ⧸ N₀), q ≠ 1 ∧ ψ q = q := by
    by_contra h
    have hfpf : MonoidHom.FixedPointFree (ψ : (↥Y ⧸ N₀) → (↥Y ⧸ N₀)) := by
      intro q hq
      by_contra hq1
      exact h ⟨q, hq1, hq⟩
    have hodd := MonoidHom.FixedPointFree.odd_card_of_involutive hfpf hψ2
    exact (Nat.not_odd_iff_even.mpr heven) hodd
  obtain ⟨q, hq1, hqfix⟩ := hex
  obtain ⟨y, hyq⟩ := QuotientGroup.mk_surjective q
  have hq1' : QuotientGroup.mk y ≠ 1 := hyq ▸ hq1
  have hqfix' : ψ (QuotientGroup.mk y) = QuotientGroup.mk y := hyq ▸ hqfix
  have hφy_eq : QuotientGroup.mk (s := N₀) (φ y) = QuotientGroup.mk (s := N₀) y := by
    rw [← hψapply y]
    exact hqfix'
  have hzN : (φ y) / y ∈ N₀ := QuotientGroup.eq_iff_div_mem.mp hφy_eq
  let zY : ↥Y := (φ y) / y
  have hzN' : zY ∈ N₀ := hzN
  have hzZ0 : (zY : G) ∈ X.Z 0 := Subgroup.mem_subgroupOf.mp hzN'
  have hyNZ0 : (y : G) ∉ X.Z 0 := by
    intro hyZ
    have hyN : y ∈ N₀ := Subgroup.mem_subgroupOf.mpr hyZ
    exact hq1' ((QuotientGroup.eq_one_iff (N := N₀) y).mpr hyN)
  have hyz : y * zY = φ y := by
    dsimp [zY]
    calc y * (φ y / y) = (y * φ y) * y⁻¹ := by
          rw [div_eq_mul_inv]; group
      _ = (φ y * y) * y⁻¹ := by rw [mul_comm' y (φ y)]
      _ = φ y := by group
  have hzY2 : zY ^ 2 = 1 := by
    apply Subtype.ext
    simpa using Z_zero_sq X hb hc hGT hs hodd h5 hX hn0 hzZ0
  have hzYinv : zY⁻¹ = zY := by
    have h : zY * zY = 1 := by simpa [pow_two] using hzY2
    exact inv_eq_of_mul_eq_one_left h
  have hφz : φ zY = zY := by
    have hφy : φ y = y * zY := hyz.symm
    calc φ zY = φ (φ y / y) := by rfl
      _ = φ (φ y) / φ y := map_div φ (φ y) y
      _ = y / (y * zY) := by rw [hφ2 y, hφy]
      _ = zY⁻¹ := by
          calc y / (y * zY) = y * (y * zY)⁻¹ := by rw [div_eq_mul_inv]
            _ = y * (zY⁻¹ * y⁻¹) := by rw [mul_inv_rev]
            _ = (y * zY⁻¹) * y⁻¹ := by group
            _ = (zY⁻¹ * y) * y⁻¹ := by rw [mul_comm' y zY⁻¹]
            _ = zY⁻¹ := by group
      _ = zY := hzYinv
  have hz_conj : s * (zY : G) * s⁻¹ = (zY : G) := by
    have h := congrArg (fun t : ↥Y => (t : G)) hφz
    simpa [hφapply] using h
  have hQ0centZ : X.Q 0 ≤ Subgroup.centralizer ({(zY : G)} : Set G) :=
    Q_zero_le_centralizer_singleton X hzZ0
  have hzcentS : (zY : G) ∈ Subgroup.centralizer (X.S : Set G) := by
    have h := mem_centralizer_sup_zpowers_of_fixed (Q := X.Q 0) (s := s) (u := (zY : G))
      hQ0centZ hz_conj
    rwa [← hSsup] at h
  have hZ0normBot : X.Z 0 ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top
  have hzRel : (zY : G) ∈ relCent (X.Z 0) ⊥ X.S := by
    rw [mem_relCent hZ0normBot]
    refine ⟨hzZ0, ?_⟩
    intro a ha
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.mp hzcentS a ha).symm
  have hzZ1 : (zY : G) ∈ X.Z 1 := by
    rw [X.Z_one_eq_relCent hb hc hGT hs hodd h5 hX]
    exact hzRel
  let fY : ↥Y →* ↥Y :=
    { toFun := fun a => a * (φ a)⁻¹
      map_one' := by simp
      map_mul' := by
        intro a b
        calc (a * b) * (φ (a * b))⁻¹
            = (a * b) * (φ a * φ b)⁻¹ := by rw [map_mul]
          _ = a * b * ((φ b)⁻¹ * (φ a)⁻¹) := by rw [mul_inv_rev]
          _ = a * (b * (φ b)⁻¹) * (φ a)⁻¹ := by group
          _ = a * ((b * (φ b)⁻¹) * (φ a)⁻¹) := by group
          _ = a * ((φ a)⁻¹ * (b * (φ b)⁻¹)) := by
              rw [mul_comm' (b * (φ b)⁻¹) (φ a)⁻¹]
          _ = (a * (φ a)⁻¹) * (b * (φ b)⁻¹) := by group }
  let f : X.Z 0 →* ↥Y := fY.comp (Subgroup.inclusion hZ0Y)
  have hf_y : fY y = zY := by
    dsimp [fY, zY]
    rw [div_eq_mul_inv]
    calc y * (φ y)⁻¹ = (φ y * y⁻¹)⁻¹ := by rw [mul_inv_rev, inv_inv]
      _ = φ y * y⁻¹ := by
          rw [show (φ y * y⁻¹) = zY from by dsimp [zY]; rw [div_eq_mul_inv]]
          exact hzYinv
  have hrange_le : f.range ≤ (X.Z 1).subgroupOf Y := by
    intro v hv
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hv
    rw [Subgroup.mem_subgroupOf]
    have hmem : ⁅(w : G), s⁆ ∈ ⁅X.Z 0, X.S⁆ :=
      Subgroup.commutator_mem_commutator w.2 hsS
    rw [X.commutator_Z_zero_S hb hc hGT hs hodd h5 hX] at hmem
    have hf_eq : ((f w : ↥Y) : G) = ⁅(w : G), s⁆ := by
      dsimp [f, fY]
      rw [hφapply]
      change (w : G) * (s * (w : G) * s⁻¹)⁻¹ = (w : G) * s * (w : G)⁻¹ * s⁻¹
      group
    rwa [hf_eq]
  have hrange_ne_bot : f.range ≠ ⊥ := by
    intro hbot
    have hφfixZ : ∀ w : X.Z 0, φ ⟨w, hZ0Y w.2⟩ = ⟨w, hZ0Y w.2⟩ := by
      intro w
      have hfm : f w = 1 := by
        have hmem : f w ∈ f.range := MonoidHom.mem_range.mpr ⟨w, rfl⟩
        rw [hbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      dsimp [f, fY] at hfm
      have h2 : Subgroup.inclusion hZ0Y w = φ (Subgroup.inclusion hZ0Y w) := by
        calc Subgroup.inclusion hZ0Y w
            = ((Subgroup.inclusion hZ0Y w) * (φ (Subgroup.inclusion hZ0Y w))⁻¹) *
                φ (Subgroup.inclusion hZ0Y w) := by group
          _ = 1 * φ (Subgroup.inclusion hZ0Y w) := by rw [hfm]
          _ = φ (Subgroup.inclusion hZ0Y w) := one_mul _
      exact h2.symm
    have hZ0centS : X.Z 0 ≤ Subgroup.centralizer (X.S : Set G) := by
      intro w hw
      have hQcent : X.Q 0 ≤ Subgroup.centralizer ({w} : Set G) :=
        Q_zero_le_centralizer_singleton X hw
      have hfix : s * w * s⁻¹ = w := by
        have h := congrArg (fun t : ↥Y => (t : G)) (hφfixZ ⟨w, hw⟩)
        simpa [hφapply] using h
      have h := mem_centralizer_sup_zpowers_of_fixed (Q := X.Q 0) (s := s) (u := w)
        hQcent hfix
      rwa [← hSsup] at h
    have hZ1bot : X.Z 1 = ⊥ := by
      rw [← X.commutator_Z_zero_S hb hc hGT hs hodd h5 hX]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hZ0centS
    exact hZ1neBot hZ1bot
  have hrange_card : Nat.card ↥f.range = 2 := by
    have hle_card : Nat.card ↥f.range ≤ Nat.card ↥((X.Z 1).subgroupOf Y) :=
      Subgroup.card_le_of_le hrange_le
    have hlt : 1 < Nat.card ↥f.range :=
      Finite.one_lt_card_iff_nontrivial.mpr
        ((Subgroup.nontrivial_iff_ne_bot f.range).mpr hrange_ne_bot)
    omega
  have hrange_eq : f.range = (X.Z 1).subgroupOf Y := by
    refine Subgroup.eq_of_le_of_card_ge hrange_le ?_
    rw [hZ1subcard, hrange_card]
  have hz_range : zY ∈ f.range := by
    rw [hrange_eq]
    exact Subgroup.mem_subgroupOf.mpr hzZ1
  obtain ⟨w, hw⟩ := MonoidHom.mem_range.mp hz_range
  have hf_w : fY ⟨w, hZ0Y w.2⟩ = zY := by
    simpa [f, Subgroup.inclusion] using hw
  let u : ↥Y := y * (⟨w, hZ0Y w.2⟩ : ↥Y)⁻¹
  have hu_fix : φ u = u := by
    have hf_u : fY u = 1 := by
      calc fY u = fY y * (fY ⟨w, hZ0Y w.2⟩)⁻¹ := by
            dsimp [u]; rw [map_mul, map_inv]
        _ = zY * zY⁻¹ := by rw [hf_y, hf_w]
        _ = 1 := by group
    have h1 : u * (φ u)⁻¹ = 1 := hf_u
    have h2 : u = φ u := by
      calc u = (u * (φ u)⁻¹) * φ u := by group
        _ = 1 * φ u := by rw [h1]
        _ = φ u := one_mul _
    exact h2.symm
  have hu_conj : s * (u : G) * s⁻¹ = (u : G) := by
    have h := congrArg (fun t : ↥Y => (t : G)) hu_fix
    simpa [hφapply] using h
  have hQ0centU : X.Q 0 ≤ Subgroup.centralizer ({(u : G)} : Set G) := by
    intro qq hq
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact Subgroup.mem_centralizer_iff.mp (hQ0leCentY hq) (u : G) u.2
  have hu_centS : (u : G) ∈ Subgroup.centralizer (X.S : Set G) := by
    have h := mem_centralizer_sup_zpowers_of_fixed (Q := X.Q 0) (s := s) (u := (u : G))
      hQ0centU hu_conj
    rwa [← hSsup] at h
  have huZ0 : (u : G) ∈ X.Z 0 :=
    mem_Z_zero_of_mem_Q_zero_of_mem_centralizer_S X (hYQ0 u.2) hu_centS
  have hy_eq_u : (y : G) = (u : G) * (w : G) := by
    dsimp [u]
    group
  have hyZ0' : (y : G) ∈ X.Z 0 := by
    rw [hy_eq_u]
    exact (X.Z 0).mul_mem huZ0 w.2
  exact hyNZ0 hyZ0'

private theorem exists_moves_Z_zero (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) :
    ∃ l ∈ X.L 1, ∃ v ∈ X.Vone, ⁅l, v⁆ ∉ X.Z 1 := by
  obtain ⟨g, hgL, hg02⟩ := (X.hyp.isLocL2_oTwoPrime (X.vert 1)).trans (X.vert 0) (X.vert 2)
    (X.adj 0).symm (X.adj 1)
  have hgZ : conjSub g (X.Z 0) = X.Z 2 := X.Z_conj hg02
  have hZ2ne : X.Z 2 ≠ X.Z 0 := by
    intro h
    exact X.Z_two_not_le_Q_zero hb hGT hs hodd h5 hX
      (h ▸ X.Z_le_Q 0)
  by_contra h
  push Not at h
  have hle : conjSub g (X.Z 0) ≤ X.Z 0 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
    have hcomm : ⁅g, z⁆ ∈ X.Z 1 := h g hgL z (Z_zero_le_Vone X hz)
    have hz1 : g * z * g⁻¹ ∈ X.Z 0 := by
      have h1 : g * z * g⁻¹ = ⁅g, z⁆ * z := by
        rw [commutatorElement_def]; group
      rw [h1]
      exact (X.Z 0).mul_mem
        ((Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le hcomm) hz
    simpa [MulAut.conj_apply] using hz1
  haveI : Finite ↥(X.Z 0) :=
    finite_of_le_stabilizer X.hyp (H := X.Z 0) (X.Z_le_Q 0 |>.trans (X.Q_le_Gi 0))
  have hcard : Nat.card ↥(conjSub g (X.Z 0)) = Nat.card ↥(X.Z 0) :=
    CFSG.Quasithin.St84.card_conjSub g (X.Z 0)
  have heq : conjSub g (X.Z 0) = X.Z 0 :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)
  exact hZ2ne (hgZ.symm.trans heq)

private theorem false_of_normal_between (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) {N : Subgroup G}
    (hZ1N : X.Z 1 ≤ N) (hZ1Nlt : X.Z 1 < N)
    (hNV : N ≤ X.Vone) (hNne : N ≠ X.Vone)
    (hNnorm : X.L 1 ≤ Subgroup.normalizer (N : Set G))
    (hirrN : ∀ M : Subgroup G, X.Z 1 ≤ M → M ≤ N →
      X.L 1 ≤ Subgroup.normalizer (M : Set G) → M = X.Z 1 ∨ M = N) : False := by
  have hNZ0 : N ⊓ X.Z 0 = X.Z 1 :=
    normal_between_inf_Z_zero X hb hc hGT hs hodd h5 hX hn0 hZ1N hNV hNne hNnorm
  have hNcommQ : ⁅N ⊓ X.Q (-1), X.Q 0⁆ ≤ X.Z 1 :=
    normal_between_commutator_inf_Q_neg_one X hb hc hGT hs hodd h5 hX hn0
      hNV hNZ0 hNnorm
  have hYnormal : X.L 0 ≤ Subgroup.normalizer
      (((N ⊓ X.Q (-1)) ⊔ X.Z 0 : Subgroup G) : Set G) :=
    normal_between_Y_normal X hb hc hGT hs hodd h5 hX hn0 hn1 hNV hNnorm
  have hYcomm : ⁅(N ⊓ X.Q (-1)) ⊔ X.Z 0, X.Q 0⁆ = ⊥ :=
    normal_between_Y_commutator X hb hc hGT hs hodd h5 hX hn0
      hNcommQ hYnormal
  have hNQm : N ⊓ X.Q (-1) = X.Z 1 :=
    normal_between_inf_Q_neg_one X hb hc hGT hs hodd h5 hX hn0 hZ1N hNV hNZ0
      hYnormal hYcomm
  have hrel8 : (X.Z 1).relIndex N ≤ 8 :=
    normal_between_relIndex_le_eight X hb hc hGT hs hodd h5 hX hn0 hn1
      hZ1N hNV hNQm
  have hNcomm : ⁅N, X.L 1⁆ ≤ X.Z 1 :=
    normal_between_centralizes X hb hc hGT hs hodd h5 hX hn0 hn1
      hZ1N hNV hNnorm hirrN hrel8
  have hNQ0 : N ≤ X.Q 0 :=
    normal_between_le_Q_zero X hb hc hGT hs hodd h5 hX hn0 hn1
      hNV hNcomm
  have hrel2 : (X.Z 1).relIndex N = 2 :=
    normal_between_relIndex_eq_two X hb hc hGT hs hodd h5 hX hn0
      hZ1N hNV hZ1Nlt hirrN hNcomm
  exact false_of_normal_between_Q_zero X hb hc hGT hs hodd h5 hX hn0 hn1
    hZ1N hNQ0 hNQm hrel2 hNcomm

private theorem irreducible_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) :
    ∀ W : Subgroup G, X.Z 1 ≤ W → W ≤ X.Vone →
      X.L 1 ≤ Subgroup.normalizer (W : Set G) →
      W = X.Z 1 ∨ W = X.Vone := by
  classical
  intro W hZ1W hWV hWnorm
  by_cases hW1 : W = X.Z 1
  · exact Or.inl hW1
  by_cases hWVeq : W = X.Vone
  · exact Or.inr hWVeq
  exfalso
  have hVQ1 : X.Vone ≤ X.Q 1 :=
    X.Vone_le_Q_one hGT hs hodd h5 hX
  have hVGi1 : X.Vone ≤ X.Gi 1 :=
    hVQ1.trans ((le_oTwoPrime_of_isPGroup (pCoreOf_isPGroup' (X.Gi 1))
      (X.Q_le_Gi 1)).trans (X.L_le_Gi 1))
  haveI : Finite ↥W := finite_of_le_stabilizer X.hyp (H := W) (hWV.trans hVGi1)
  let P : ℕ → Prop := fun n => ∃ N : Subgroup G, X.Z 1 ≤ N ∧ N ≤ W ∧
    X.L 1 ≤ Subgroup.normalizer (N : Set G) ∧ N ≠ X.Z 1 ∧ Nat.card N = n
  have hP : ∃ n, P n := ⟨Nat.card W, W, hZ1W, le_rfl, hWnorm, hW1, rfl⟩
  let m := Nat.find hP
  obtain ⟨N, hZ1N, hNW, hNnorm, hNne1, hNcard⟩ := Nat.find_spec hP
  have hNV : N ≤ X.Vone := hNW.trans hWV
  have hNneV : N ≠ X.Vone := by
    intro h
    exact hWVeq (le_antisymm hWV (h ▸ hNW))
  have hZ1Nlt : X.Z 1 < N := lt_of_le_of_ne hZ1N (Ne.symm hNne1)
  haveI : Finite ↥N := finite_of_le_stabilizer X.hyp (H := N) (hNV.trans hVGi1)
  have hirrN : ∀ M : Subgroup G, X.Z 1 ≤ M → M ≤ N →
      X.L 1 ≤ Subgroup.normalizer (M : Set G) → M = X.Z 1 ∨ M = N := by
    intro M hZ1M hMN hMnorm
    by_cases hM1 : M = X.Z 1
    · exact Or.inl hM1
    · right
      have hMW : M ≤ W := hMN.trans hNW
      have hcardM : Nat.card M = Nat.card N := by
        apply le_antisymm
        · exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hMN)
        · calc Nat.card N = m := hNcard
            _ ≤ Nat.card M := Nat.find_min' hP ⟨M, hZ1M, hMW, hMnorm, hM1, rfl⟩
      exact Subgroup.eq_of_le_of_card_ge hMN (le_of_eq hcardM.symm)
  exact false_of_normal_between X hb hc hGT hs hodd h5 hX hn0 hn1
    hZ1N hZ1Nlt hNV hNneV hNnorm hirrN

theorem card_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) :
    Nat.card X.Vone = 2 ^ 5 := by
  have hirr := irreducible_Vone X hb hc hGT hs hodd h5 hX hn0 hn1
  have hnt := exists_moves_Z_zero X hb hc hGT hs hodd h5 hX hn0
  have h16 := relIndex_Z_one_Vone_eq_sixteen X hb hc hGT hs hodd h5 hX hn0 hn1 hirr hnt
  have hZ1V : X.Z 1 ≤ X.Vone :=
    (Z_one_lt_Z_zero X hb hc hGT hs hodd h5 hX hn0).le.trans (Z_zero_le_Vone X)
  have hrel := Subgroup.relIndex_mul_card (H := X.Z 1) (K := X.Vone)
  rw [inf_of_le_left hZ1V, h16] at hrel
  have hcardZ1 : Nat.card (X.Z 1) = 2 :=
    card_Z_one_eq_two X hb hc hGT hs hodd h5 hX hn0
  rw [hcardZ1] at hrel
  simpa using hrel.symm

theorem Vone_inf_Q_neg_one (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) :
    X.Vone ⊓ X.Q (-1) = X.Z 0 := by
  have hVcard : Nat.card X.Vone = 32 := by
    rw [card_Vone X hb hc hGT hs hodd h5 hX hn0 hn1]
    norm_num
  haveI : Finite ↥(X.Q 0) := finite_of_le_stabilizer X.hyp (X.Q_le_Gi 0)
  have hcardA : Nat.card ↥(X.Vone ⊓ X.Q 0) = 16 :=
    card_Vone_inf_Q_zero X hb hc hGT hs hodd h5 hX hn0 hVcard
  let A : Subgroup G := X.Vone ⊓ X.Q 0
  let B : Subgroup G := X.VnegOne ⊓ X.Q 0
  let C : Subgroup G := X.Q 1 ⊓ X.Q (-1)
  let Y : Subgroup G := A ⊔ C
  have hQ0 := X.Q_zero_eq_sup hb hc hGT hs hodd h5 hX
  have hQ0' : X.Q 0 = B ⊔ Y := by
    change X.Q 0 = (X.VnegOne ⊓ X.Q 0) ⊔
      ((X.Vone ⊓ X.Q 0) ⊔ (X.Q 1 ⊓ X.Q (-1)))
    nth_rewrite 1 [hQ0]
    ac_rfl
  have hA_le_Q1 : A ≤ X.Q 1 :=
    (inf_le_left.trans (X.Vone_le_Q_one hGT hs hodd h5 hX))
  have hC_le_Q1 : C ≤ X.Q 1 := inf_le_left
  have hY_le_Q1 : Y ≤ X.Q 1 := sup_le hA_le_Q1 hC_le_Q1
  have hB_le_Q0 : B ≤ X.Q 0 := inf_le_right
  have hA_le_G0 : A ≤ X.Gi 0 := inf_le_right.trans (X.Q_le_Gi 0)
  have hQ0_le_G1 : X.Q 0 ≤ X.Gi 1 := by
    intro q hq
    exact (X.Q_le_Gi_adj 0 hq).2
  have hQ0_le_Gm1 : X.Q 0 ≤ X.Gi (-1) := by
    intro q hq
    exact (X.Q_le_Gi_adj 0 hq).1
  have hQ0normV : X.Q 0 ≤ Subgroup.normalizer (X.Vone : Set G) :=
    hQ0_le_G1.trans (Gi_one_le_normalizer_Vone X)
  have hQ0normA : X.Q 0 ≤ Subgroup.normalizer (A : Set G) := by
    refine (le_inf hQ0normV (Subgroup.le_normalizer)).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := X.Vone) (K := X.Q 0)
  have hQ0normQ1 : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) := by
    refine hQ0_le_G1.trans ?_
    change X.Gi 1 ≤ Subgroup.normalizer (pCoreOf 2 (X.Gi 1))
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)
  have hQ0normQm1 : X.Q 0 ≤ Subgroup.normalizer (X.Q (-1) : Set G) :=
    hQ0_le_Gm1.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi (-1)))
  have hQ0normC : X.Q 0 ≤ Subgroup.normalizer (C : Set G) := by
    refine (le_inf hQ0normQ1 hQ0normQm1).trans ?_
    exact Subgroup.inf_normalizer_le_normalizer_inf (H := X.Q 1) (K := X.Q (-1))
  have hQ0normY : X.Q 0 ≤ Subgroup.normalizer (Y : Set G) :=
    CFSG.Quasithin.F1.le_normalizer_sup hQ0normA hQ0normC
  have hBnormY : B ≤ Subgroup.normalizer (Y : Set G) := hB_le_Q0.trans hQ0normY
  have hBC : X.Q 1 ⊓ B ≤ C :=
    le_inf inf_le_left
      ((inf_le_right : X.Q 1 ⊓ B ≤ B).trans
        (inf_le_left.trans (X.VnegOne_le_Q_neg_one hb hGT hs hodd h5 hX)))
  have hBCY : X.Q 1 ⊓ B ≤ Y := hBC.trans le_sup_right
  have hDed := Subgroup.inf_sup_assoc_of_le (H := B) (K := X.Q 1) (N := Y)
    hBnormY hY_le_Q1
  have hQ1Q0 : X.Q 1 ⊓ X.Q 0 = Y := by
    rw [hQ0', ← hDed, sup_eq_right.mpr hBCY]
  have hQ01 : X.Q 0 ⊓ X.Q 1 = Y := by rw [inf_comm]; exact hQ1Q0
  have hAnorm : X.Gi 0 ≤ Subgroup.normalizer (C : Set G) :=
    Q_one_inf_neg_one_normal X hb hc hGT hs hodd h5 hX
  obtain ⟨-, -, hCindex, -, -⟩ := X.Q_quot_of_normal_general hc hs (by omega)
  rw [hn1] at hCindex
  norm_num at hCindex
  have hCindexY : C.relIndex Y = 4 := by
    simpa [C, inf_comm] using (hQ01 ▸ hCindex : (X.Q (-1) ⊓ X.Q 1).relIndex Y = 4)
  have hAnormC : A ≤ Subgroup.normalizer (C : Set G) := hA_le_G0.trans hAnorm
  have hprod := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
    A C (fun b hbA n hnC =>
      (Subgroup.mem_normalizer_iff.mp (hAnormC hbA) n).mp hnC)
  have hsupcard : Nat.card ↥Y = 4 * Nat.card ↥C := by
    have h := Subgroup.relIndex_mul_card (H := C) (K := Y)
    rw [hCindexY, inf_of_le_left le_sup_right] at h
    exact h.symm
  haveI hQ1fin : Finite ↥(X.Q 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Q 1) (α := X.vert 1)
      (X.Q_le_Gi 1)
  haveI hCfin : Finite ↥C :=
    Finite.of_injective _ (Subgroup.inclusion_injective (show C ≤ X.Q 1 from inf_le_left))
  have hprod' : (4 * Nat.card ↥C) * Nat.card ↥(A ⊓ C) = Nat.card ↥A * Nat.card ↥C := by
    rw [← hsupcard]
    exact hprod
  have hA16 : Nat.card ↥A = 16 := hcardA
  have hcardAC : Nat.card ↥(A ⊓ C) = 4 := by
    have h : (4 * Nat.card ↥C) * Nat.card ↥(A ⊓ C) = (4 * Nat.card ↥C) * 4 := by
      rw [hprod', hA16]
      ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.mul_pos (by norm_num) Nat.card_pos) h
  have hCQ0 : C ≤ X.Q 0 := by
    have hCG0 : C ≤ X.Gi 0 := by
      intro x hx
      exact (X.Q_le_Gi_adj 1 (Subgroup.mem_inf.mp hx).1).1
    have hC2 : IsPGroup 2 ↥C := CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 1) |>.to_le inf_le_left
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCG0 hAnorm hC2
  have hVQneg : X.Vone ⊓ X.Q (-1) = A ⊓ C := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨hxV, hxQm⟩ := Subgroup.mem_inf.mp hx
      have hxQ1 : x ∈ X.Q 1 :=
        X.Vone_le_Q_one hGT hs hodd h5 hX hxV
      have hxAC : x ∈ C := Subgroup.mem_inf.mpr ⟨hxQ1, hxQm⟩
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hxV, hCQ0 hxAC⟩, hxAC⟩
    · intro x hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).1.1, (Subgroup.mem_inf.mp hx).2.2⟩
  have hcardVQneg : Nat.card ↥(X.Vone ⊓ X.Q (-1)) = 4 := by
    rw [hVQneg, hcardAC]
  have hVQ1 : X.Vone ⊓ X.Q (-1) ≤ X.Q 1 := fun x hx =>
    X.Vone_le_Q_one hGT hs hodd h5 hX (Subgroup.mem_inf.mp hx).1
  haveI hVQfin : Finite ↥(X.Vone ⊓ X.Q (-1)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hVQ1)
  have hZ0le : X.Z 0 ≤ X.Vone ⊓ X.Q (-1) :=
    le_inf (Z_zero_le_Vone X)
      (Z_zero_le_Q_neg_one X hb hGT hs hodd h5 hX)
  have hZ0card : Nat.card (X.Z 0) = 4 :=
    card_Z_zero_eq_four X hb hc hGT hs hodd h5 hX hn0
  exact (Subgroup.eq_of_le_of_card_ge (H := X.Z 0) (K := X.Vone ⊓ X.Q (-1))
    hZ0le (by rw [hcardVQneg, hZ0card])).symm

theorem QT_inf_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) : X.QT ⊓ X.Vone = ⊥ := by
  have hVQ : X.Vone ⊓ X.Q (-1) = X.Z 0 :=
    Vone_inf_Q_neg_one X hb hc hGT hs hodd h5 hX hn0 hn1
  have hQTQ : X.QT ≤ X.Q (-1) := X.QT_le_Q (-1)
  have hle : X.QT ⊓ X.Vone ≤ X.Z 0 := by
    calc X.QT ⊓ X.Vone ≤ X.Q (-1) ⊓ X.Vone := inf_le_inf_right _ hQTQ
      _ = X.Vone ⊓ X.Q (-1) := inf_comm ..
      _ = X.Z 0 := hVQ
  have hbot : X.QT ⊓ X.Z 0 = ⊥ :=
    QT_inf_Z_eq_bot X hGT hs hodd h5 hX 0
  have hle2 : X.QT ⊓ X.Vone ≤ X.QT ⊓ X.Z 0 := le_inf inf_le_left hle
  rw [hbot] at hle2
  exact le_bot_iff.mp hle2

private theorem K_le_D_of_index (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) {D : Subgroup G} [Finite ↥D]
    (hDleL1 : D ≤ X.L 1) (hDrel_dvd : D.relIndex (X.L 1) ∣ Nat.card ↥(X.Q 1))
    (hDnorm : X.K ≤ Subgroup.normalizer (D : Set G)) :
    X.K ≤ D := by
  classical
  have hKleL1 : X.K ≤ X.L 1 := by
    rw [K_eq_Ki_one X hb hc hGT hs hodd h5 hX hn0]
    exact inf_le_right
  obtain ⟨k, hk⟩ : ∃ k, Nat.card ↥(X.Q 1) = 2 ^ k := by
    haveI : Finite ↥(X.Q 1) :=
      finite_of_le_stabilizer X.hyp (H := X.Q 1) (α := X.vert 1)
        (X.Q_le_Gi 1)
    have hQ2 : IsPGroup 2 ↥(X.Q 1) :=
      CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 1)
    exact IsPGroup.iff_card.mp hQ2
  have hDrel_pow : D.relIndex (X.L 1) ∣ 2 ^ k := by
    rwa [← hk]
  have hKrel_dvd : D.relIndex (D ⊔ X.K) ∣ Nat.card ↥X.K := by
    refine ⟨Nat.card ↥(D ⊓ X.K), ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := D) (K := D ⊔ X.K)
    rw [inf_of_le_left le_sup_left] at h1
    have h2 : Nat.card ↥(D ⊔ X.K) * Nat.card ↥(D ⊓ X.K) =
        Nat.card ↥X.K * Nat.card ↥D := by
      have hcomm : ∀ b ∈ X.K, ∀ n ∈ D, b * n * b⁻¹ ∈ D := by
        intro b hb n hn
        exact (Subgroup.mem_normalizer_iff.mp (hDnorm hb) n).mp hn
      have h := CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
        X.K D hcomm
      rwa [sup_comm (X.K) D, inf_comm (X.K) D] at h
    have h3 : Nat.card ↥D * (D.relIndex (D ⊔ X.K) * Nat.card ↥(D ⊓ X.K)) =
        Nat.card ↥D * Nat.card ↥X.K := by
      calc Nat.card ↥D * (D.relIndex (D ⊔ X.K) * Nat.card ↥(D ⊓ X.K))
          = (D.relIndex (D ⊔ X.K) * Nat.card ↥D) * Nat.card ↥(D ⊓ X.K) := by ring
        _ = Nat.card ↥(D ⊔ X.K) * Nat.card ↥(D ⊓ X.K) := by rw [h1]
        _ = Nat.card ↥X.K * Nat.card ↥D := h2
        _ = Nat.card ↥D * Nat.card ↥X.K := by ring
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h3).symm
  have hKrel_odd : Odd (D.relIndex (D ⊔ X.K)) :=
    X.odd_card_K.of_dvd_nat hKrel_dvd
  have hDKleL1 : D ⊔ X.K ≤ X.L 1 := sup_le hDleL1 hKleL1
  have hdvd : D.relIndex (D ⊔ X.K) ∣ D.relIndex (X.L 1) :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex D (D ⊔ X.K) (X.L 1) le_sup_left hDKleL1)
  have hrel_one : D.relIndex (D ⊔ X.K) = 1 :=
    CFSG.LieType.SteinbergBR.OddSylow.eq_one_of_odd_of_dvd_two_pow hKrel_odd
      (hdvd.trans hDrel_pow)
  have hKleD : X.K ≤ D := by
    have h := (Subgroup.relIndex_eq_one.mp hrel_one : D ⊔ X.K ≤ D)
    exact (le_sup_right : X.K ≤ D ⊔ X.K).trans h
  exact hKleD

theorem commutator_QT_K_eq_bot (hb : ¬ X.Z 0 ≤ X.Gi 3) (hc : CharTwoStab (V := V) (G := G))
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) : ⁅X.QT, X.K⁆ = ⊥ := by
  have hL1 : X.L 1 = X.edgeSylow 0 ⊔ X.edgeSylow 1 ⊔ X.Q 1 := by
    simpa using L_eq_edgeSylow_sup_Q X 1
  have hS : X.S = (X.VnegOne ⊓ X.Q 0) ⊔ X.Q 1 :=
    S_eq_inf_sup_Q_one X hb hc hGT hs hodd h5 hX hn0
  have hS1 : X.edgeSylow 1 = conjSub X.τ (X.Vone ⊓ X.Q 0) ⊔ X.Q 1 :=
    edgeSylow_one_eq_conj_sup_Q_one X hb hc hGT hs hodd h5 hX hn0
  let D : Subgroup G := (X.VnegOne ⊓ X.Q 0) ⊔ conjSub X.τ (X.Vone ⊓ X.Q 0)
  have hL1D : X.L 1 = D ⊔ X.Q 1 := by
    change X.L 1 = ((X.VnegOne ⊓ X.Q 0) ⊔ conjSub X.τ (X.Vone ⊓ X.Q 0)) ⊔ X.Q 1
    rw [hL1, X.edgeSylow_zero, hS, hS1]
    ac_rfl
  have hDleL1 : D ≤ X.L 1 := by rw [hL1D]; exact le_sup_left
  have hKleL1 : X.K ≤ X.L 1 := by
    rw [K_eq_Ki_one X hb hc hGT hs hodd h5 hX hn0]
    exact inf_le_right
  have hDstab : D ≤ MulAction.stabilizer G (X.vert 1) := by
    refine hDleL1.trans ?_
    rw [← Gi_one_eq_L_one X hb hc hGT hs hodd h5 hX hn0]
  haveI : Finite ↥D :=
    finite_of_le_stabilizer X.hyp (H := D) (α := X.vert 1) hDstab
  have hL1normQ : X.L 1 ≤ Subgroup.normalizer (X.Q 1 : Set G) := by
    rw [← Gi_one_eq_L_one X hb hc hGT hs hodd h5 hX hn0]
    change X.Gi 1 ≤ Subgroup.normalizer (pCoreOf 2 (X.Gi 1))
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1)
  have hDnormQ : D ≤ Subgroup.normalizer (X.Q 1 : Set G) := hDleL1.trans hL1normQ
  have hDrel_dvd : D.relIndex (X.L 1) ∣ Nat.card ↥(X.Q 1) := by
    refine ⟨Nat.card ↥(D ⊓ X.Q 1), ?_⟩
    have h1 := Subgroup.relIndex_mul_card (H := D) (K := X.L 1)
    rw [inf_of_le_left hDleL1] at h1
    have h2 : Nat.card ↥(X.L 1) * Nat.card ↥(D ⊓ X.Q 1) =
        Nat.card ↥D * Nat.card ↥(X.Q 1) := by
      rw [hL1D]
      have hcomm : ∀ b ∈ D, ∀ n ∈ X.Q 1, b * n * b⁻¹ ∈ X.Q 1 := by
        intro b hb n hn
        exact (Subgroup.mem_normalizer_iff.mp (hDnormQ hb) n).mp hn
      exact CFSG.Timmesfeld.LocalTwoSubgroups.FrobeniusFixedSpaceBounds.card_sup_mul_card_inf
        D (X.Q 1) hcomm
    have h3 : Nat.card ↥D * (D.relIndex (X.L 1) * Nat.card ↥(D ⊓ X.Q 1)) =
        Nat.card ↥D * Nat.card ↥(X.Q 1) := by
      calc Nat.card ↥D * (D.relIndex (X.L 1) * Nat.card ↥(D ⊓ X.Q 1))
          = (D.relIndex (X.L 1) * Nat.card ↥D) * Nat.card ↥(D ⊓ X.Q 1) := by ring
        _ = Nat.card ↥(X.L 1) * Nat.card ↥(D ⊓ X.Q 1) := by rw [h1]
        _ = Nat.card ↥D * Nat.card ↥(X.Q 1) := h2
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h3).symm
  have hKleD : X.K ≤ D :=
    K_le_D_of_index X hb hc hGT hs hodd h5 hX hn0 hDleL1 hDrel_dvd
      (K_le_normalizer_VnegOne_inf_Q_zero_sup X)
  have hQKleV : ⁅X.QT, X.K⁆ ≤ X.Vone :=
    (Subgroup.commutator_mono le_rfl hKleD).trans
      (commutator_QT_D_le_Vone X hb hc hGT hs hodd h5 hX)
  have hQKleQ : ⁅X.QT, X.K⁆ ≤ X.QT := by
    have h := Subgroup.le_normalizer_iff_commutator_le_right.mp X.K_le_normalizer_QT
    rwa [Subgroup.commutator_comm] at h
  have hle : ⁅X.QT, X.K⁆ ≤ X.QT ⊓ X.Vone := le_inf hQKleQ hQKleV
  rw [QT_inf_Vone X hb hc hGT hs hodd h5 hX hn0 hn1] at hle
  exact le_bot_iff.mp hle

private theorem Q_zero_le_Gi_one : X.Q 0 ≤ X.Gi 1 := by
  intro x hx
  exact (X.Q_le_Gi_adj 0 hx).2

private theorem Q_two_le_Gi_one : X.Q 2 ≤ X.Gi 1 := by
  intro x hx
  exact (X.Q_le_Gi_adj 2 hx).1

private theorem relIndex_inf_Q1_VnegOne (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) :
    ((X.VnegOne ⊓ X.Q 0) ⊓ X.Q 1).relIndex (X.VnegOne ⊓ X.Q 0) = 2 ^ X.n 1 := by
  let B := X.VnegOne ⊓ X.Q 0
  change (B ⊓ X.Q 1).relIndex B = 2 ^ X.n 1
  have hS : X.S = B ⊔ X.Q 1 :=
    S_eq_inf_sup_Q_one X hb hc hGT hs hodd h5 hX hn0
  have hQ1S : (X.Q 1).relIndex X.S = 2 ^ X.n 1 := by
    rw [← X.edgeSylow_zero]
    exact X.relIndex_Q_succ_edgeSylow 0
  have hBnorm : B ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (inf_le_right.trans (Q_zero_le_Gi_one X)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hfan := CFSG.Quasithin.Fan86.relIndex_sup_right_of_le_normalizer
    (H := B) (K := X.Q 1) hBnorm
  rw [show B ⊔ X.Q 1 = X.S from hS.symm] at hfan
  have hinf := Subgroup.inf_relIndex_left (H := B) (K := X.Q 1)
  rw [hinf, ← hfan, hQ1S]

private theorem relIndex_inf_Q1_conj_Vone (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) :
    ((conjSub X.τ (X.Vone ⊓ X.Q 0)) ⊓ X.Q 1).relIndex
      (conjSub X.τ (X.Vone ⊓ X.Q 0)) = 2 ^ X.n 1 := by
  let A2 := conjSub X.τ (X.Vone ⊓ X.Q 0)
  change (A2 ⊓ X.Q 1).relIndex A2 = 2 ^ X.n 1
  have hS : X.edgeSylow 1 = A2 ⊔ X.Q 1 :=
    edgeSylow_one_eq_conj_sup_Q_one X hb hc hGT hs hodd h5 hX hn0
  have hQ1S : (X.Q 1).relIndex (X.edgeSylow 1) = 2 ^ X.n 1 :=
    X.relIndex_Q_edgeSylow 1
  have hA2leQ2 : A2 ≤ X.Q 2 := by
    calc A2 ≤ conjSub X.τ (X.Q 0) := conjSub_mono X.τ inf_le_right
      _ = X.Q 2 := by simpa using (X.Q_add 1 0).symm
  have hA2norm : A2 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (hA2leQ2.trans (Q_two_le_Gi_one X)).trans
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (X.Gi 1))
  have hfan := CFSG.Quasithin.Fan86.relIndex_sup_right_of_le_normalizer
    (H := A2) (K := X.Q 1) hA2norm
  rw [show A2 ⊔ X.Q 1 = X.edgeSylow 1 from hS.symm] at hfan
  have hinf := Subgroup.inf_relIndex_left (H := A2) (K := X.Q 1)
  rw [hinf, ← hfan, hQ1S]

private theorem orderOf_nbrRep_dvd_pow_two {H : Subgroup G} (hH2 : IsPGroup 2 ↥H)
    (hHG : H ≤ X.Gi 1) (hn1 : X.n 1 = 2) {g : G} (hg : g ∈ H) :
    ∃ k, orderOf (X.nbrRep 1 hn1 ⟨g, hHG hg⟩) ∣ 2 ^ k := by
  haveI : Finite ↥H :=
    finite_of_le_stabilizer X.hyp (H := H) (α := X.vert 1)
      hHG
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH2
  refine ⟨k, ?_⟩
  let φ : ↥H →* Equiv.Perm (Fin 5) := (X.nbrRep 1 hn1).comp (Subgroup.inclusion hHG)
  have h1' : orderOf ((X.nbrRep 1 hn1) ((Subgroup.inclusion hHG) ⟨g, hg⟩)) ∣
      orderOf (⟨g, hg⟩ : ↥H) := by
    have := orderOf_map_dvd φ ⟨g, hg⟩
    simpa [φ] using this
  have h1 : orderOf (X.nbrRep 1 hn1 ⟨g, hHG hg⟩) ∣ orderOf (⟨g, hg⟩ : ↥H) := by
    simpa [Subgroup.inclusion] using h1'
  have h2 : orderOf (⟨g, hg⟩ : ↥H) ∣ Nat.card ↥H := orderOf_dvd_natCard _
  rw [hk] at h2
  exact h1.trans h2

private theorem eq_one_of_order_dvd_pow_two_and_three {g : Equiv.Perm (Fin 5)}
    (h2 : ∃ k, orderOf g ∣ 2 ^ k) (h3 : orderOf g ∣ 3) : g = 1 := by
  obtain ⟨k, hk⟩ := h2
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((by decide : Nat.Coprime 2 3).pow_left k) hk h3)

private theorem exists_mem_inf_notMem_of_card_eq_mul {B Q C : Subgroup G} [Finite ↥B]
    {m : ℕ} (hm : 2 < m) (hcard : Nat.card ↥B = m * Nat.card ↥(B ⊓ Q))
    (hbound : Nat.card ↥B ≤ 2 * Nat.card ↥(B ⊓ C)) :
    ∃ e ∈ B, e ∈ C ∧ e ∉ Q := by
  by_contra h
  push Not at h
  have hcle : B ⊓ C ≤ B ⊓ Q := by
    intro e he
    obtain ⟨heB, heC⟩ := Subgroup.mem_inf.mp he
    exact Subgroup.mem_inf.mpr ⟨heB, h e heB heC⟩
  haveI hBCfin : Finite ↥(B ⊓ C) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (show B ⊓ C ≤ B from inf_le_left))
  haveI hBQfin : Finite ↥(B ⊓ Q) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (show B ⊓ Q ≤ B from inf_le_left))
  have hcardle : Nat.card ↥(B ⊓ C) ≤ Nat.card ↥(B ⊓ Q) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hcle)
  have hcontr : m * Nat.card ↥(B ⊓ Q) ≤ 2 * Nat.card ↥(B ⊓ Q) := by
    calc m * Nat.card ↥(B ⊓ Q) = Nat.card ↥B := hcard.symm
      _ ≤ 2 * Nat.card ↥(B ⊓ C) := hbound
      _ ≤ 2 * Nat.card ↥(B ⊓ Q) := Nat.mul_le_mul_left 2 hcardle
  have hm2 : m ≤ 2 := Nat.le_of_mul_le_mul_right hcontr Nat.card_pos
  omega

private theorem two_pow_pred_le_relIndex {B Q C : Subgroup G} [Finite ↥B] {k : ℕ}
    (hk : 1 ≤ k) (hcard : Nat.card ↥B = 2 ^ k * Nat.card ↥(B ⊓ Q))
    (hbound : Nat.card ↥B ≤ 2 * Nat.card ↥(B ⊓ C)) :
    2 ^ (k - 1) ≤ Q.relIndex (B ⊓ C) := by
  haveI hBCfin : Finite ↥(B ⊓ C) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (show B ⊓ C ≤ B from inf_le_left))
  haveI hBQfin : Finite ↥(B ⊓ Q) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (show B ⊓ Q ≤ B from inf_le_left))
  haveI hQBCfin : Finite ↥(Q ⊓ (B ⊓ C)) :=
    Finite.of_injective _
      (Subgroup.inclusion_injective (show Q ⊓ (B ⊓ C) ≤ B ⊓ C from inf_le_right))
  have hpow : 2 ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h1 : 2 ^ (k - 1) * Nat.card ↥(B ⊓ Q) ≤ Nat.card ↥(B ⊓ C) := by
    have h2 : 2 * (2 ^ (k - 1) * Nat.card ↥(B ⊓ Q)) ≤
        2 * Nat.card ↥(B ⊓ C) := by
      calc 2 * (2 ^ (k - 1) * Nat.card ↥(B ⊓ Q))
          = (2 * 2 ^ (k - 1)) * Nat.card ↥(B ⊓ Q) := by ring
        _ = 2 ^ k * Nat.card ↥(B ⊓ Q) := by rw [hpow]
        _ = Nat.card ↥B := hcard.symm
        _ ≤ 2 * Nat.card ↥(B ⊓ C) := hbound
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num)
  have hle : Nat.card ↥(Q ⊓ (B ⊓ C)) ≤ Nat.card ↥(B ⊓ Q) := by
    refine Subgroup.card_le_of_le ?_
    calc Q ⊓ (B ⊓ C) ≤ Q ⊓ B := inf_le_inf_left Q inf_le_left
      _ = B ⊓ Q := inf_comm Q B
  have h1' : 2 ^ (k - 1) * Nat.card ↥(Q ⊓ (B ⊓ C)) ≤ Nat.card ↥(B ⊓ C) := by
    calc 2 ^ (k - 1) * Nat.card ↥(Q ⊓ (B ⊓ C))
        ≤ 2 ^ (k - 1) * Nat.card ↥(B ⊓ Q) := Nat.mul_le_mul_left _ hle
      _ ≤ Nat.card ↥(B ⊓ C) := h1
  have hrel := Subgroup.relIndex_mul_card (H := Q) (K := B ⊓ C)
  have hpos : 0 < Nat.card ↥(Q ⊓ (B ⊓ C)) := Nat.card_pos
  rw [← hrel] at h1'
  exact Nat.le_of_mul_le_mul_right h1' hpos

private theorem card_eq_pow_mul_inf_Q_one {B : Subgroup G} [Finite ↥B]
    (hidx : (B ⊓ X.Q 1).relIndex B = 2 ^ X.n 1) :
    Nat.card ↥B = 2 ^ X.n 1 * Nat.card ↥(B ⊓ X.Q 1) := by
  have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := B)
  have hidx' : (X.Q 1).relIndex B = 2 ^ X.n 1 := by
    rw [← Subgroup.inf_relIndex_left (H := B) (K := X.Q 1)]
    simpa [inf_comm] using hidx
  rw [hidx', inf_comm] at h
  exact h.symm

private theorem exists_mem_inf_notMem_and_two_pow_le_relIndex {B : Subgroup G}
    [Finite ↥B] {q : G} (hn1 : 3 ≤ X.n 1)
    (hcard : Nat.card ↥B = 2 ^ X.n 1 * Nat.card ↥(B ⊓ X.Q 1))
    (hbound : Nat.card ↥B ≤
      2 * Nat.card ↥(B ⊓ Subgroup.centralizer ({q} : Set G))) :
    ∃ e ∈ B, e ∈ Subgroup.centralizer ({q} : Set G) ∧ e ∉ X.Q 1 ∧
      2 ^ (X.n 1 - 1) ≤
        (X.Q 1).relIndex (B ⊓ Subgroup.centralizer ({q} : Set G)) := by
  obtain ⟨e, heB, heCq, heQ1⟩ :=
    exists_mem_inf_notMem_of_card_eq_mul (B := B) (Q := X.Q 1)
      (C := Subgroup.centralizer ({q} : Set G)) (m := 2 ^ X.n 1)
      (by
        calc 2 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ X.n 1 := Nat.pow_le_pow_right (by norm_num) (by omega))
      hcard hbound
  exact ⟨e, heB, heCq, heQ1,
    two_pow_pred_le_relIndex (B := B) (Q := X.Q 1)
      (C := Subgroup.centralizer ({q} : Set G)) (by omega) hcard hbound⟩

private theorem transitive_centralizer_of_three_le (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hGT : Even (Nat.card X.GT)) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hn1 : 3 ≤ X.n 1) {q : G}
    (hAc : 2 ^ (X.n 1 - 1) ≤
      (X.Q 1).relIndex ((X.VnegOne ⊓ X.Q 0) ⊓ Subgroup.centralizer ({q} : Set G)))
    (hBQ : ¬ (conjSub X.τ (X.Vone ⊓ X.Q 0)) ⊓
      Subgroup.centralizer ({q} : Set G) ≤ X.Q 1) :
    ∀ a b : V, Γ.Adj (X.vert 1) a → Γ.Adj (X.vert 1) b →
      ∃ g ∈ Subgroup.centralizer ({q} : Set G) ⊓ X.Gi 1, g • a = b := by
  let B : Subgroup G := X.VnegOne ⊓ X.Q 0
  let A2 : Subgroup G := conjSub X.τ (X.Vone ⊓ X.Q 0)
  let Cq : Subgroup G := Subgroup.centralizer ({(q : G)} : Set G)
  have hQ0S : X.Q 0 ≤ X.S := by
    rw [← X.edgeSylow_zero]
    exact X.Q_le_edgeSylow_left 0
  have hSleL1 : X.S ≤ X.L 1 := by
    have h := (X.isSylowTwoOf_edgeSylow_L_succ 0).1
    rwa [X.edgeSylow_zero] at h
  have hB_le_Gi0 : B ≤ X.Gi 0 :=
    (inf_le_left.trans (X.VnegOne_le_Q_neg_one hb hGT hs hodd h5 hX)).trans (by
      have h := (X.Q_le_Gi_adj (-1)).trans inf_le_right
      simpa using h)
  have hB_le_L1 : B ≤ X.L 1 := (inf_le_right.trans hQ0S).trans hSleL1
  have hA2_le_Q2 : A2 ≤ X.Q 2 := by
    calc A2 ≤ conjSub X.τ (X.Q 0) := conjSub_mono X.τ inf_le_right
      _ = X.Q 2 := by simpa using (X.Q_add 1 0).symm
  have hA2_le_Gi2 : A2 ≤ X.Gi 2 := hA2_le_Q2.trans (X.Q_le_Gi 2)
  have hA2_le_L1 : A2 ≤ X.L 1 :=
    (hA2_le_Q2.trans (X.Q_le_edgeSylow 1)).trans (X.edgeSylow_le_L 1)
  have hB2grp : IsPGroup 2 ↥B :=
    (CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 0)).to_le
      (inf_le_right : B ≤ X.Q 0)
  have hA2grp : IsPGroup 2 ↥A2 :=
    (CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 2)).to_le hA2_le_Q2
  have hAgrp : IsPGroup 2 ↥(B ⊓ Cq) := hB2grp.to_le inf_le_left
  have hBgrp : IsPGroup 2 ↥(A2 ⊓ Cq) := hA2grp.to_le inf_le_left
  intro a b ha hb
  obtain ⟨g, hg, hgab⟩ := X.transitive_of_two_pGroups 1 hn1
    (H := Cq) (A := B ⊓ Cq) (B := A2 ⊓ Cq)
    inf_le_right inf_le_right
    (inf_le_left.trans hB_le_L1) (inf_le_left.trans hA2_le_L1)
    hAgrp hBgrp
    (inf_le_left.trans hB_le_Gi0) (inf_le_left.trans hA2_le_Gi2)
    hAc hBQ ha hb
  exact ⟨g, ⟨hg.1, X.L_le_Gi 1 hg.2⟩, hgab⟩

theorem false_of_n_zero_eq_one_of_three_le_n_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : 3 ≤ X.n 1) : False := by
  obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (X.QT_ne_bot hGT)
  have hqQT : (q : G) ∈ X.QT := q.2
  have hqne : (q : G) ≠ 1 := by
    intro h
    exact hq1 (Subtype.ext h)
  let B : Subgroup G := X.VnegOne ⊓ X.Q 0
  let A2 : Subgroup G := conjSub X.τ (X.Vone ⊓ X.Q 0)
  let Cq : Subgroup G := Subgroup.centralizer ({(q : G)} : Set G)
  have hBindex : (B ⊓ X.Q 1).relIndex B = 2 ^ X.n 1 := by
    change ((X.VnegOne ⊓ X.Q 0) ⊓ X.Q 1).relIndex (X.VnegOne ⊓ X.Q 0) = 2 ^ X.n 1
    exact relIndex_inf_Q1_VnegOne X hb hc hGT hs hodd h5 hX hn0
  have hA2index : (A2 ⊓ X.Q 1).relIndex A2 = 2 ^ X.n 1 := by
    change ((conjSub X.τ (X.Vone ⊓ X.Q 0)) ⊓ X.Q 1).relIndex
      (conjSub X.τ (X.Vone ⊓ X.Q 0)) = 2 ^ X.n 1
    exact relIndex_inf_Q1_conj_Vone X hb hc hGT hs hodd h5 hX hn0
  haveI hBfin : Finite ↥B :=
    finite_of_le_stabilizer X.hyp (H := B) (α := X.vert 0)
      (inf_le_right.trans (X.Q_le_Gi 0))
  haveI hA2fin : Finite ↥A2 :=
    finite_of_le_stabilizer X.hyp (H := A2) (α := X.vert 2)
      ((conjSub_mono X.τ inf_le_right).trans (by
        rw [show conjSub X.τ (X.Q 0) = X.Q 2 by
          simpa [pow_one] using (X.Q_add 1 0).symm]) |>.trans (X.Q_le_Gi 2))
  have hBcard : Nat.card ↥B = 2 ^ X.n 1 * Nat.card ↥(B ⊓ X.Q 1) :=
    card_eq_pow_mul_inf_Q_one X hBindex
  have hA2card : Nat.card ↥A2 = 2 ^ X.n 1 * Nat.card ↥(A2 ⊓ X.Q 1) :=
    card_eq_pow_mul_inf_Q_one X hA2index
  have hBbound : Nat.card ↥B ≤ 2 * Nat.card ↥(B ⊓ Cq) := by
    change Nat.card ↥(X.VnegOne ⊓ X.Q 0) ≤
      2 * Nat.card ↥(X.VnegOne ⊓ X.Q 0 ⊓ Subgroup.centralizer ({(q : G)} : Set G))
    exact card_centralizer_VnegOne_le_two X hb hc hGT hs hodd h5 hX hn0 hqQT
  have hA2bound : Nat.card ↥A2 ≤ 2 * Nat.card ↥(A2 ⊓ Cq) := by
    change Nat.card (conjSub X.τ (X.Vone ⊓ X.Q 0)) ≤
      2 * Nat.card ↥(conjSub X.τ (X.Vone ⊓ X.Q 0) ⊓
        Subgroup.centralizer ({(q : G)} : Set G))
    exact card_centralizer_conj_Vone_le_two X hb hc hGT hs hodd h5 hX hn0 hqQT
  obtain ⟨-, -, -, -, hAc⟩ :=
    exists_mem_inf_notMem_and_two_pow_le_relIndex X (B := B) hn1 hBcard hBbound
  obtain ⟨f, hfA2, hfCq, hfQ1, -⟩ :=
    exists_mem_inf_notMem_and_two_pow_le_relIndex X (B := A2) hn1 hA2card hA2bound
  have hBQ : ¬ A2 ⊓ Cq ≤ X.Q 1 := by
    intro hle
    exact hfQ1 (hle ⟨hfA2, hfCq⟩)
  exact not_centralizer_transitive_one X hb hc hGT hs hodd h5 hX hn0 hqQT hqne
    (transitive_centralizer_of_three_le X hb hGT hs hodd h5 hX hn1 hAc hBQ)

theorem false_of_n_zero_eq_one_of_n_one_eq_two (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : X.n 1 = 2) : False := by
  let ρ := X.nbrRep 1 hn1
  obtain ⟨q, hq1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (X.QT_ne_bot hGT)
  have hqQT : (q : G) ∈ X.QT := q.2
  have hqne : (q : G) ≠ 1 := by
    intro h
    exact hq1 (Subtype.ext h)
  have hKQT : X.K ≤ Subgroup.centralizer (X.QT : Set G) := by
    have hcomm : ⁅X.K, X.QT⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact commutator_QT_K_eq_bot X hb hc hGT hs hodd h5 hX hn0 hn1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hKq : X.K ≤ Subgroup.centralizer ({(q : G)} : Set G) :=
    hKQT.trans (Subgroup.centralizer_le (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact hx ▸ q.2))
  have hKleL1 : X.K ≤ X.L 1 := by
    rw [K_eq_Ki_one X hb hc hGT hs hodd h5 hX hn0]
    exact inf_le_right
  have hKcard : Nat.card ↥X.K = 3 := by
    rw [K_eq_Ki_one X hb hc hGT hs hodd h5 hX hn0, X.card_Ki 1, hn1]
    norm_num
  haveI hKfin : Finite ↥X.K := finite_of_le_stabilizer X.hyp (X.K_le_Gi 1)
  have hQ1pow : ∃ k : ℕ, Nat.card ↥(X.Q 1) = 2 ^ k := by
    haveI : Finite ↥(X.Q 1) :=
      finite_of_le_stabilizer X.hyp (H := X.Q 1) (α := X.vert 1)
        (X.Q_le_Gi 1)
    exact IsPGroup.iff_card.mp (CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 1))
  have hKQ1 : X.K ⊓ X.Q 1 = ⊥ := by
    obtain ⟨k, hk⟩ := hQ1pow
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    rw [hKcard, hk]
    exact (by decide : Nat.Coprime 3 2).pow_right k
  have hKne : X.K ≠ ⊥ := by
    intro h
    rw [h] at hKcard
    simp at hKcard
  obtain ⟨k, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
  have hkK : (k : G) ∈ X.K := k.2
  have hkne : (k : G) ≠ 1 := by
    intro h
    exact hk1 (Subtype.ext h)
  have hρrange : ρ.range = alternatingGroup (Fin 5) := by
    have h := X.nbrRep_map_L 1 hn1
    have hL : X.L 1 = X.Gi 1 :=
      (Gi_one_eq_L_one X hb hc hGT hs hodd h5 hX hn0).symm
    rw [hL, Subgroup.subgroupOf_self, Subgroup.map_top] at h
    simpa [ρ] using h
  have hρkA : ρ ⟨k, X.K_le_Gi 1 hkK⟩ ∈ alternatingGroup (Fin 5) := by
    rw [← hρrange]
    exact MonoidHom.mem_range.mpr ⟨⟨k, X.K_le_Gi 1 hkK⟩, rfl⟩
  have hρkne : ρ ⟨k, X.K_le_Gi 1 hkK⟩ ≠ 1 := by
    intro h
    have hker : (⟨k, X.K_le_Gi 1 hkK⟩ : ↥(X.Gi 1)) ∈ ρ.ker := h
    have hmem : (⟨k, X.K_le_Gi 1 hkK⟩ : ↥(X.Gi 1)) ∈
        ρ.ker ⊓ (X.L 1).subgroupOf (X.Gi 1) := ⟨hker, hKleL1 hkK⟩
    rw [X.nbrRep_ker_inf_L 1 hn1] at hmem
    have hkQ1 : (k : G) ∈ X.Q 1 := Subgroup.mem_subgroupOf.mp hmem
    have hbot : (k : G) ∈ (⊥ : Subgroup G) := by
      rw [← hKQ1]
      exact ⟨hkK, hkQ1⟩
    exact hkne (Subgroup.mem_bot.mp hbot)
  let w0 : ↥(X.nbrAction 1) := ⟨X.vert 0, X.mem_nbrAction.mpr ((X.adj 0).symm)⟩
  let w2 : ↥(X.nbrAction 1) := ⟨X.vert 2, X.mem_nbrAction.mpr (X.adj 1)⟩
  let a : Fin 5 := X.nbrEquiv 1 hn1 w0
  let b : Fin 5 := X.nbrEquiv 1 hn1 w2
  have hab : a ≠ b := by
    intro h
    have h' := (X.nbrEquiv 1 hn1).injective h
    have hv : X.vert 0 = X.vert 2 := congrArg Subtype.val h'
    exact (X.vert_injective.ne (by norm_num : (0 : ℤ) ≠ 2)) hv
  have hρka : ρ ⟨k, X.K_le_Gi 1 hkK⟩ a = a := by
    change ρ ⟨k, X.K_le_Gi 1 hkK⟩ (X.nbrEquiv 1 hn1 w0) = X.nbrEquiv 1 hn1 w0
    rw [X.nbrRep_apply 1 hn1]
    congr 1
    apply Subtype.ext
    exact X.K_fix k hkK 0
  have hρkb : ρ ⟨k, X.K_le_Gi 1 hkK⟩ b = b := by
    change ρ ⟨k, X.K_le_Gi 1 hkK⟩ (X.nbrEquiv 1 hn1 w2) = X.nbrEquiv 1 hn1 w2
    rw [X.nbrRep_apply 1 hn1]
    congr 1
    apply Subtype.ext
    exact X.K_fix k hkK 2
  have hρkcube : (ρ ⟨k, X.K_le_Gi 1 hkK⟩) ^ 3 = 1 :=
    CFSG.alternatingGroup_cube_eq_one_of_fixes_two _ hρkA a b hab hρka hρkb
  let B : Subgroup G := X.VnegOne ⊓ X.Q 0
  let A2 : Subgroup G := conjSub X.τ (X.Vone ⊓ X.Q 0)
  have hBindex : (B ⊓ X.Q 1).relIndex B = 4 := by
    have h := relIndex_inf_Q1_VnegOne X hb hc hGT hs hodd h5 hX hn0
    change ((X.VnegOne ⊓ X.Q 0) ⊓ X.Q 1).relIndex (X.VnegOne ⊓ X.Q 0) = 4
    rw [hn1] at h
    simpa using h
  have hA2index : (A2 ⊓ X.Q 1).relIndex A2 = 4 := by
    have h := relIndex_inf_Q1_conj_Vone X hb hc hGT hs hodd h5 hX hn0
    change ((conjSub X.τ (X.Vone ⊓ X.Q 0)) ⊓ X.Q 1).relIndex
      (conjSub X.τ (X.Vone ⊓ X.Q 0)) = 4
    rw [hn1] at h
    simpa using h
  haveI hBfin : Finite ↥B :=
    finite_of_le_stabilizer X.hyp (H := B) (α := X.vert 1)
      (inf_le_right.trans (Q_zero_le_Gi_one X))
  haveI hA2fin : Finite ↥A2 :=
    finite_of_le_stabilizer X.hyp (H := A2) (α := X.vert 1)
      (((conjSub_mono X.τ inf_le_right).trans (by
        rw [show conjSub X.τ (X.Q 0) = X.Q 2 by
          simpa [pow_one] using (X.Q_add 1 0).symm]) |>.trans (Q_two_le_Gi_one X)))
  haveI hBQ1fin : Finite ↥(B ⊓ X.Q 1) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (show B ⊓ X.Q 1 ≤ B from inf_le_left))
  haveI hA2Q1fin : Finite ↥(A2 ⊓ X.Q 1) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (show A2 ⊓ X.Q 1 ≤ A2 from inf_le_left))
  have hBbound : Nat.card ↥B ≤
      2 * Nat.card ↥(B ⊓ Subgroup.centralizer ({(q : G)} : Set G)) := by
    change Nat.card ↥(X.VnegOne ⊓ X.Q 0) ≤
      2 * Nat.card ↥(X.VnegOne ⊓ X.Q 0 ⊓ Subgroup.centralizer ({(q : G)} : Set G))
    exact card_centralizer_VnegOne_le_two X hb hc hGT hs hodd h5 hX hn0 hqQT
  have hA2bound : Nat.card ↥A2 ≤
      2 * Nat.card ↥(A2 ⊓ Subgroup.centralizer ({(q : G)} : Set G)) := by
    change Nat.card (conjSub X.τ (X.Vone ⊓ X.Q 0)) ≤
      2 * Nat.card ↥(conjSub X.τ (X.Vone ⊓ X.Q 0) ⊓ Subgroup.centralizer ({(q : G)} : Set G))
    exact card_centralizer_conj_Vone_le_two X hb hc hGT hs hodd h5 hX hn0 hqQT
  have hBcard : Nat.card ↥B = 4 * Nat.card ↥(B ⊓ X.Q 1) := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := B)
    have hidx : (X.Q 1).relIndex B = 4 := by
      rw [← Subgroup.inf_relIndex_left (H := B) (K := X.Q 1)]
      simpa [inf_comm] using hBindex
    rw [hidx, inf_comm] at h
    exact h.symm
  have hA2card : Nat.card ↥A2 = 4 * Nat.card ↥(A2 ⊓ X.Q 1) := by
    have h := Subgroup.relIndex_mul_card (H := X.Q 1) (K := A2)
    have hidx : (X.Q 1).relIndex A2 = 4 := by
      rw [← Subgroup.inf_relIndex_left (H := A2) (K := X.Q 1)]
      simpa [inf_comm] using hA2index
    rw [hidx, inf_comm] at h
    exact h.symm
  have hexB : ∃ e : G, e ∈ B ∧ e ∈ Subgroup.centralizer ({(q : G)} : Set G) ∧ e ∉ X.Q 1 := by
    by_contra h
    push Not at h
    have hcle : B ⊓ Subgroup.centralizer ({(q : G)} : Set G) ≤ B ⊓ X.Q 1 := by
      intro e he
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp he).1,
        h e (Subgroup.mem_inf.mp he).1 (Subgroup.mem_inf.mp he).2⟩
    haveI hCqfin : Finite ↥(B ⊓ Subgroup.centralizer ({(q : G)} : Set G)) :=
      Finite.of_injective _
        (Subgroup.inclusion_injective
          (show B ⊓ Subgroup.centralizer ({(q : G)} : Set G) ≤ B from inf_le_left))
    have hcardle : Nat.card ↥(B ⊓ Subgroup.centralizer ({(q : G)} : Set G)) ≤
        Nat.card ↥(B ⊓ X.Q 1) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hcle)
    have hcontr : 4 * Nat.card ↥(B ⊓ X.Q 1) ≤ 2 * Nat.card ↥(B ⊓ X.Q 1) := by
      calc 4 * Nat.card ↥(B ⊓ X.Q 1) = Nat.card ↥B := hBcard.symm
        _ ≤ 2 * Nat.card ↥(B ⊓ Subgroup.centralizer ({(q : G)} : Set G)) := hBbound
        _ ≤ 2 * Nat.card ↥(B ⊓ X.Q 1) := Nat.mul_le_mul_left 2 hcardle
    have hpos : 0 < Nat.card ↥(B ⊓ X.Q 1) := Nat.card_pos
    omega
  obtain ⟨e, heB, heCq, heQ1⟩ := hexB
  have hA2leQ2 : A2 ≤ X.Q 2 := by
    calc A2 ≤ conjSub X.τ (X.Q 0) := conjSub_mono X.τ inf_le_right
      _ = X.Q 2 := by simpa using (X.Q_add 1 0).symm
  have hA2p : IsPGroup 2 ↥A2 :=
    (CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 2)).to_le hA2leQ2
  have hexA2 : ∃ f : G, f ∈ A2 ∧ f ∈ Subgroup.centralizer ({(q : G)} : Set G) ∧ f ∉ X.Q 1 := by
    by_contra h
    push Not at h
    have hcle : A2 ⊓ Subgroup.centralizer ({(q : G)} : Set G) ≤ A2 ⊓ X.Q 1 := by
      intro f hf
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hf).1,
        h f (Subgroup.mem_inf.mp hf).1 (Subgroup.mem_inf.mp hf).2⟩
    haveI hA2cfin : Finite ↥(A2 ⊓ Subgroup.centralizer ({(q : G)} : Set G)) :=
      Finite.of_injective _
        (Subgroup.inclusion_injective
          (show A2 ⊓ Subgroup.centralizer ({(q : G)} : Set G) ≤ A2 from inf_le_left))
    have hcardle : Nat.card ↥(A2 ⊓ Subgroup.centralizer ({(q : G)} : Set G)) ≤
        Nat.card ↥(A2 ⊓ X.Q 1) :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hcle)
    have hcontr : 4 * Nat.card ↥(A2 ⊓ X.Q 1) ≤ 2 * Nat.card ↥(A2 ⊓ X.Q 1) := by
      calc 4 * Nat.card ↥(A2 ⊓ X.Q 1) = Nat.card ↥A2 := hA2card.symm
        _ ≤ 2 * Nat.card ↥(A2 ⊓ Subgroup.centralizer ({(q : G)} : Set G)) := hA2bound
        _ ≤ 2 * Nat.card ↥(A2 ⊓ X.Q 1) := Nat.mul_le_mul_left 2 hcardle
    have hpos : 0 < Nat.card ↥(A2 ⊓ X.Q 1) := Nat.card_pos
    omega
  obtain ⟨f, hfA2, hfCq, hfQ1⟩ := hexA2
  have heG1 : e ∈ X.Gi 1 := Q_zero_le_Gi_one X (Subgroup.mem_inf.mp heB).2
  have hfG1 : f ∈ X.Gi 1 := (hA2leQ2.trans (Q_two_le_Gi_one X)) hfA2
  have hρeA : ρ ⟨e, heG1⟩ ∈ alternatingGroup (Fin 5) := by
    rw [← hρrange]
    exact MonoidHom.mem_range.mpr ⟨⟨e, heG1⟩, rfl⟩
  have hρfA : ρ ⟨f, hfG1⟩ ∈ alternatingGroup (Fin 5) := by
    rw [← hρrange]
    exact MonoidHom.mem_range.mpr ⟨⟨f, hfG1⟩, rfl⟩
  have hρene : ρ ⟨e, heG1⟩ ≠ 1 := by
    intro h
    have hker : (⟨e, heG1⟩ : ↥(X.Gi 1)) ∈ ρ.ker := h
    have hmem : (⟨e, heG1⟩ : ↥(X.Gi 1)) ∈
        ρ.ker ⊓ (X.L 1).subgroupOf (X.Gi 1) :=
      ⟨hker, Subgroup.mem_subgroupOf.mpr (by
        rw [← Gi_one_eq_L_one X hb hc hGT hs hodd h5 hX hn0]
        exact heG1)⟩
    rw [X.nbrRep_ker_inf_L 1 hn1] at hmem
    exact heQ1 (Subgroup.mem_subgroupOf.mp hmem)
  have hρfne : ρ ⟨f, hfG1⟩ ≠ 1 := by
    intro h
    have hker : (⟨f, hfG1⟩ : ↥(X.Gi 1)) ∈ ρ.ker := h
    have hmem : (⟨f, hfG1⟩ : ↥(X.Gi 1)) ∈
        ρ.ker ⊓ (X.L 1).subgroupOf (X.Gi 1) :=
      ⟨hker, Subgroup.mem_subgroupOf.mpr (by
        rw [← Gi_one_eq_L_one X hb hc hGT hs hodd h5 hX hn0]
        exact hfG1)⟩
    rw [X.nbrRep_ker_inf_L 1 hn1] at hmem
    exact hfQ1 (Subgroup.mem_subgroupOf.mp hmem)
  have heQ0 : e ∈ X.Q 0 := (Subgroup.mem_inf.mp heB).2
  have hfQ2 : f ∈ X.Q 2 := hA2leQ2 hfA2
  have hefix0 : e • X.vert 0 = X.vert 0 :=
    MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 0 heQ0)
  have hffix2 : f • X.vert 2 = X.vert 2 :=
    MulAction.mem_stabilizer_iff.mp (X.Q_le_Gi 2 hfQ2)
  have hρea : ρ ⟨e, heG1⟩ a = a := by
    change ρ ⟨e, heG1⟩ (X.nbrEquiv 1 hn1 w0) = X.nbrEquiv 1 hn1 w0
    rw [X.nbrRep_apply 1 hn1]
    congr 1
    apply Subtype.ext
    exact hefix0
  have hρfb : ρ ⟨f, hfG1⟩ b = b := by
    change ρ ⟨f, hfG1⟩ (X.nbrEquiv 1 hn1 w2) = X.nbrEquiv 1 hn1 w2
    rw [X.nbrRep_apply 1 hn1]
    congr 1
    apply Subtype.ext
    exact hffix2
  have hQ0p : IsPGroup 2 ↥(X.Q 0) :=
    CFSG.Quasithin.St84.pCoreOf_isPGroup' (X.Gi 0)
  have hρeb : ρ ⟨e, heG1⟩ b ≠ b := by
    intro hb
    have hcube := CFSG.alternatingGroup_cube_eq_one_of_fixes_two
      _ hρeA a b hab hρea hb
    have h3 : orderOf (ρ ⟨e, heG1⟩) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hcube
    have h2 : ∃ k, orderOf (ρ ⟨e, heG1⟩) ∣ 2 ^ k :=
      orderOf_nbrRep_dvd_pow_two X hQ0p (Q_zero_le_Gi_one X) hn1 heQ0
    exact hρene (eq_one_of_order_dvd_pow_two_and_three h2 h3)
  have hρfa : ρ ⟨f, hfG1⟩ a ≠ a := by
    intro ha
    have hcube := CFSG.alternatingGroup_cube_eq_one_of_fixes_two
      _ hρfA a b hab ha hρfb
    have h3 : orderOf (ρ ⟨f, hfG1⟩) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact hcube
    have h2 : ∃ k, orderOf (ρ ⟨f, hfG1⟩) ∣ 2 ^ k :=
      orderOf_nbrRep_dvd_pow_two X hA2p ((hA2leQ2.trans (Q_two_le_Gi_one X))) hn1 hfA2
    exact hρfne (eq_one_of_order_dvd_pow_two_and_three h2 h3)
  let CqG1 : Subgroup ↥(X.Gi 1) :=
    (Subgroup.centralizer ({(q : G)} : Set G) ⊓ X.Gi 1).subgroupOf (X.Gi 1)
  let H : Subgroup (Equiv.Perm (Fin 5)) := CqG1.map ρ
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hρkord : orderOf (ρ ⟨k, X.K_le_Gi 1 hkK⟩) = 3 :=
    orderOf_eq_prime hρkcube hρkne
  have hρk2A : (ρ ⟨k, X.K_le_Gi 1 hkK⟩) ^ 2 ∈ alternatingGroup (Fin 5) :=
    Subgroup.pow_mem _ hρkA 2
  have hρk2ne : (ρ ⟨k, X.K_le_Gi 1 hkK⟩) ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf (ρ ⟨k, X.K_le_Gi 1 hkK⟩) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact h
    rw [hρkord] at hdvd
    norm_num at hdvd
  let rk : Equiv.Perm (Fin 5) := ρ ⟨k, X.K_le_Gi 1 hkK⟩
  have h3set : ∀ x : Fin 5, x ≠ a → x ≠ b →
      ({x, rk x, (rk ^ 2) x} : Set (Fin 5)) = {a, b}ᶜ := by
    intro x hxa hxb
    have hx1 : rk x ≠ x := by
      intro h
      have h1 : rk = 1 :=
        CFSG.alternatingGroup_eq_one_of_fixes_three rk hρkA x a b
          hxa hxb hab h hρka hρkb
      exact hρkne h1
    have hx2 : (rk ^ 2) x ≠ x := by
      intro h
      have h2a : (rk ^ 2) a = a := by
        rw [pow_two, Equiv.Perm.mul_apply, hρka, hρka]
      have h2b : (rk ^ 2) b = b := by
        rw [pow_two, Equiv.Perm.mul_apply, hρkb, hρkb]
      have h1 : rk ^ 2 = 1 :=
        CFSG.alternatingGroup_eq_one_of_fixes_three (rk ^ 2) hρk2A x a b
          hxa hxb hab h h2a h2b
      exact hρk2ne h1
    have hx3 : rk x ≠ (rk ^ 2) x := by
      intro h
      have h' := congrArg (fun z => rk⁻¹ z) h
      have hx : x = rk x := by
        simpa [pow_two, Equiv.Perm.mul_apply] using h'
      exact hx1 hx.symm
    have hrka_inv : rk⁻¹ a = a := by
      conv_lhs => rw [← hρka]
      exact Equiv.symm_apply_apply rk a
    have hrkb_inv : rk⁻¹ b = b := by
      conv_lhs => rw [← hρkb]
      exact Equiv.symm_apply_apply rk b
    have hTcard : ({x, rk x, (rk ^ 2) x} : Set (Fin 5)).ncard = 3 := by
      rw [Set.ncard_insert_of_notMem (by
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
            exact ⟨hx1.symm, hx2.symm⟩),
        Set.ncard_insert_of_notMem (by simpa using hx3), Set.ncard_singleton]
    have hCcard : ({a, b}ᶜ : Set (Fin 5)).ncard = 3 := by
      rw [Set.ncard_compl, Set.ncard_pair hab]
      norm_num
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      rcases hy with rfl | rfl | rfl
      · exact ⟨hxa, hxb⟩
      · refine ⟨?_, ?_⟩
        · intro h
          have h' := congrArg (fun z => rk⁻¹ z) h
          have hxa' : x = a := by simpa [hrka_inv] using h'
          exact hxa hxa'
        · intro h
          have h' := congrArg (fun z => rk⁻¹ z) h
          have hxb' : x = b := by simpa [hrkb_inv] using h'
          exact hxb hxb'
      · refine ⟨?_, ?_⟩
        · intro h
          have h' := congrArg (fun z => ((rk ^ 2)⁻¹) z) h
          have h2a : (rk ^ 2) a = a := by
            rw [pow_two, Equiv.Perm.mul_apply, hρka, hρka]
          have h2a_inv : ((rk ^ 2)⁻¹) a = a := by
            conv_lhs => rw [← h2a]
            exact Equiv.symm_apply_apply (rk ^ 2) a
          have hxa' : x = a := by simpa [h2a_inv] using h'
          exact hxa hxa'
        · intro h
          have h' := congrArg (fun z => ((rk ^ 2)⁻¹) z) h
          have h2b : (rk ^ 2) b = b := by
            rw [pow_two, Equiv.Perm.mul_apply, hρkb, hρkb]
          have h2b_inv : ((rk ^ 2)⁻¹) b = b := by
            conv_lhs => rw [← h2b]
            exact Equiv.symm_apply_apply (rk ^ 2) b
          have hxb' : x = b := by simpa [h2b_inv] using h'
          exact hxb hxb'
    · rw [hTcard, hCcard]
  let tk : ↥CqG1 := ⟨⟨k, X.K_le_Gi 1 hkK⟩, by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hKq hkK, X.K_le_Gi 1 hkK⟩⟩
  let te : ↥CqG1 := ⟨⟨e, heG1⟩, by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨heCq, heG1⟩⟩
  let tf : ↥CqG1 := ⟨⟨f, hfG1⟩, by
    rw [Subgroup.mem_subgroupOf]
    exact ⟨hfCq, hfG1⟩⟩
  let Orb : Set (Fin 5) := {y | ∃ t : ↥CqG1, ρ t a = y}
  have hOrb_mul : ∀ t : ↥CqG1, ∀ y ∈ Orb, ρ t y ∈ Orb := by
    rintro t y ⟨s, rfl⟩
    refine ⟨t * s, ?_⟩
    simp only [Subgroup.coe_mul, map_mul, Equiv.Perm.mul_apply]
  have hc_Orb : ρ tf a ∈ Orb := ⟨tf, rfl⟩
  have hca : ρ tf a ≠ a := hρfa
  have hcb : ρ tf a ≠ b := by
    intro h
    have h' : ρ tf a = ρ tf b := by rw [h, hρfb]
    have hab' : a = b := (ρ tf).injective h'
    exact hab hab'
  have hOrb_univ : Orb = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    by_cases hza : z = a
    · subst z
      exact ⟨1, by simp⟩
    by_cases hzb : z = b
    · subst z
      have hρeb_Orb : ρ te b ∈ Orb := by
        have hne_a : ρ te b ≠ a := by
          intro h
          have h' : ρ te b = ρ te a := by rw [h, hρea]
          exact hab ((ρ te).injective h'.symm)
        have hne_b : ρ te b ≠ b := hρeb
        have hset := h3set (ρ tf a) hca hcb
        have hmem : ρ te b ∈ ({a, b}ᶜ : Set (Fin 5)) := by
          simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
          exact ⟨hne_a, hne_b⟩
        rw [← hset] at hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with h | h | h
        · rw [h]
          exact hc_Orb
        · rw [h]
          exact hOrb_mul tk (ρ tf a) hc_Orb
        · rw [h]
          exact hOrb_mul tk (ρ tk (ρ tf a)) (hOrb_mul tk (ρ tf a) hc_Orb)
      obtain ⟨s, hs⟩ := hρeb_Orb
      refine ⟨te⁻¹ * s, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
        Equiv.Perm.mul_apply]
      rw [hs]
      exact Equiv.symm_apply_apply (ρ te) b
    · have hset := h3set (ρ tf a) hca hcb
      have hmem : z ∈ ({a, b}ᶜ : Set (Fin 5)) := by
        simp only [Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
        exact ⟨hza, hzb⟩
      rw [← hset] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h | h | h
      · rw [h]
        exact hc_Orb
      · rw [h]
        exact hOrb_mul tk (ρ tf a) hc_Orb
      · rw [h]
        exact hOrb_mul tk (ρ tk (ρ tf a)) (hOrb_mul tk (ρ tf a) hc_Orb)
  have htrans : ∀ x y : V, Γ.Adj (X.vert 1) x → Γ.Adj (X.vert 1) y →
      ∃ g ∈ Subgroup.centralizer ({(q : G)} : Set G) ⊓ X.Gi 1, g • x = y := by
    intro x y hx hy
    let wx : ↥(X.nbrAction 1) := ⟨x, X.mem_nbrAction.mpr hx⟩
    let wy : ↥(X.nbrAction 1) := ⟨y, X.mem_nbrAction.mpr hy⟩
    let px : Fin 5 := X.nbrEquiv 1 hn1 wx
    let py : Fin 5 := X.nbrEquiv 1 hn1 wy
    have hpx : px ∈ Orb := by rw [hOrb_univ]; exact Set.mem_univ _
    have hpy : py ∈ Orb := by rw [hOrb_univ]; exact Set.mem_univ _
    obtain ⟨tx, hxeq⟩ := hpx
    obtain ⟨ty, hyeq⟩ := hpy
    let t : ↥CqG1 := ty * tx⁻¹
    have ht : ρ t px = py := by
      simp only [t, Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv,
        Equiv.Perm.mul_apply]
      have htxinv : (ρ tx)⁻¹ px = a := by
        rw [← hxeq]
        exact Equiv.symm_apply_apply (ρ tx) a
      rw [htxinv, hyeq]
    let g : G := (t : ↥(X.Gi 1))
    have hgCq : g ∈ Subgroup.centralizer ({(q : G)} : Set G) :=
      (Subgroup.mem_subgroupOf.mp t.2).1
    have hgG1 : g ∈ X.Gi 1 := (Subgroup.mem_subgroupOf.mp t.2).2
    refine ⟨g, ⟨hgCq, hgG1⟩, ?_⟩
    have hmap : X.nbrEquiv 1 hn1 ((⟨g, hgG1⟩ : ↥(X.Gi 1)) • wx) = py := by
      rw [← X.nbrRep_apply 1 hn1]
      exact ht
    have hsub : (⟨g, hgG1⟩ : ↥(X.Gi 1)) • wx = wy :=
      (X.nbrEquiv 1 hn1).injective hmap
    exact congrArg Subtype.val hsub
  exact not_centralizer_transitive_one X hb hc hGT hs hodd h5 hX hn0
    hqQT hqne htrans

theorem false_of_n_zero_eq_one (hb : ¬ X.Z 0 ≤ X.Gi 3)
    (hc : CharTwoStab (V := V) (G := G)) (hGT : Even (Nat.card X.GT))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hn0 : X.n 0 = 1) (hn1 : 2 ≤ X.n 1) : False := by
  rcases Nat.eq_or_lt_of_le hn1 with h | h
  · exact false_of_n_zero_eq_one_of_n_one_eq_two X hb hc hGT hs hodd h5 hX hn0 h.symm
  · exact false_of_n_zero_eq_one_of_three_le_n_one X hb hc hGT hs hodd h5 hX hn0 (by omega)

end Setup

end CFSG.Quasithin.St84
