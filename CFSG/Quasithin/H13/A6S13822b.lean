module

public import CFSG.Quasithin.H13.A6S13822a
public import CFSG.Quasithin.H13.A6S13813g
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.A6S13816a

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace A6Gen

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_perfect_of_solvable {Q : Type*} [Group Q] (hperf : commutator Q = ⊤)
    [hs : Group.IsSolvable Q] (q : Q) : q = 1 := by
  obtain ⟨n, hn⟩ := hs.solvable
  have htop : ∀ k, derivedSeries Q k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf]
  rw [htop n] at hn
  have : q ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top q
  exact (Subgroup.mem_bot).1 this

omit [Finite G] in
theorem conj_mem_commutator {K X : Subgroup G} {k n : G} (hk : k ∈ K) (hn : n ∈ ⁅K, X⁆) :
    k * n * k⁻¹ ∈ ⁅K, X⁆ := by
  have hle : ⁅K, X⁆ ≤ (⁅K, X⁆).comap (MulAut.conj k).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha x hx
    show k * ⁅a, x⁆ * k⁻¹ ∈ ⁅K, X⁆
    have e : k * ⁅a, x⁆ * k⁻¹ = ⁅k * a, x⁆ * ⁅k, x⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (K.mul_mem hk ha) hx)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hk hx))
  exact hle hn

omit [Finite G] in
theorem normal_le_center_or_eq_top {Q : Type*} [Group Q] (hperf : Group.IsPerfect Q)
    (hs : IsSimpleGroup (Q ⧸ Subgroup.center Q)) (N : Subgroup Q) (hN : N.Normal) :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  let qt := QuotientGroup.mk' (Subgroup.center Q)
  have hnormal : (N.map qt).Normal := Subgroup.Normal.map hN qt (QuotientGroup.mk'_surjective _)
  rcases hnormal.eq_bot_or_eq_top with hbot | htop
  · left
    have hkernel : N ≤ qt.ker := N.map_eq_bot_iff.mp hbot
    change N ≤ (QuotientGroup.mk' (Subgroup.center Q)).ker at hkernel
    simpa only [QuotientGroup.ker_mk'] using hkernel
  · right
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have hcomap := Subgroup.comap_map_eq qt N
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at hcomap
      exact hcomap.symm
    have hderived : commutator Q ≤ N :=
      Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup inferInstance
    rw [Group.IsPerfect.commutator_eq_top] at hderived
    exact top_unique hderived

theorem comm_eq_of_not_le {K X : Subgroup G} (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hperf : ⁅K, K⁆ = K) (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hn : ¬ ⁅K, X⁆ ≤ pCoreOf 2 K) : ⁅K, X⁆ = K := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := ⁅K, X⁆ with hNdef
  have hNK : N ≤ K := by
    rw [hNdef, Subgroup.commutator_le]
    intro k hk x hx
    rw [commutatorElement_def]
    have : x * k⁻¹ * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hXK hx) k⁻¹).mp (K.inv_mem hk)
    rw [show k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) by group]
    exact K.mul_mem hk this
  have hperfK : commutator ↥K = ⊤ := (Subgroup.isPerfect_iff.mpr hperf).commutator_eq_top
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  set N₀ := N.subgroupOf K with hN₀
  have hN₀n : N₀.Normal := ⟨fun n hn k => by
    rw [hN₀, Subgroup.mem_subgroupOf] at hn ⊢
    exact conj_mem_commutator k.2 hn⟩
  have hN' : (N₀.map π).Normal := hN₀n.map π (QuotientGroup.mk'_surjective _)
  rcases normal_le_center_or_eq_top hq.1 hq.2.1 (N₀.map π) hN' with hc | htop
  · exfalso
    apply hn
    rw [hNdef, Subgroup.commutator_le]
    intro k hk x hx
    have hcK : ∀ k' : ↥K, ⁅(k' : G), x⁆ ∈ K := fun k' =>
      hNK (Subgroup.commutator_mem_commutator k'.2 hx)
    have hcZ : ∀ k' : ↥K, π ⟨⁅(k' : G), x⁆, hcK k'⟩ ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) :=
      fun k' => hc ⟨⟨_, hcK k'⟩, Subgroup.mem_subgroupOf.2
        (Subgroup.commutator_mem_commutator k'.2 hx), rfl⟩
    let δ : ↥K →* ↥(Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
      { toFun := fun k' => ⟨π ⟨⁅(k' : G), x⁆, hcK k'⟩, hcZ k'⟩
        map_one' := by
          apply Subtype.ext
          simp only [OneMemClass.coe_one]
          convert map_one π using 2
          exact Subtype.ext (by simp [commutatorElement_def])
        map_mul' := fun a b => by
          apply Subtype.ext
          have e : (⟨⁅((a * b : ↥K) : G), x⁆, hcK (a * b)⟩ : ↥K) =
              a * ⟨⁅(b : G), x⁆, hcK b⟩ * a⁻¹ * ⟨⁅(a : G), x⁆, hcK a⟩ :=
            Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv,
              commutatorElement_def]; group)
          show π ⟨⁅((a * b : ↥K) : G), x⁆, hcK (a * b)⟩ =
            π ⟨⁅(a : G), x⁆, hcK a⟩ * π ⟨⁅(b : G), x⁆, hcK b⟩
          rw [e, map_mul, map_mul, map_mul, map_inv]
          have hzb : π a * π ⟨⁅(b : G), x⁆, hcK b⟩ = π ⟨⁅(b : G), x⁆, hcK b⟩ * π a :=
            Subgroup.mem_center_iff.mp (hcZ b) (π a)
          have hza : π ⟨⁅(b : G), x⁆, hcK b⟩ * π ⟨⁅(a : G), x⁆, hcK a⟩ =
              π ⟨⁅(a : G), x⁆, hcK a⟩ * π ⟨⁅(b : G), x⁆, hcK b⟩ :=
            Subgroup.mem_center_iff.mp (hcZ a) _
          calc π a * π ⟨⁅(b : G), x⁆, hcK b⟩ * (π a)⁻¹ * π ⟨⁅(a : G), x⁆, hcK a⟩ =
              π ⟨⁅(b : G), x⁆, hcK b⟩ * π ⟨⁅(a : G), x⁆, hcK a⟩ := by
                rw [hzb, mul_inv_cancel_right]
            _ = _ := hza }
    have hδ : ∀ k' : ↥K, δ k' = 1 := by
      intro k'
      have hmem : k' ∈ commutator ↥K := hperfK ▸ Subgroup.mem_top k'
      exact Abelianization.commutator_subset_ker δ hmem
    have h1 := congrArg Subtype.val (hδ ⟨k, hk⟩)
    have h3 : π ⟨⁅k, x⁆, hcK ⟨k, hk⟩⟩ = 1 := h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff] at h3
    exact h3
  ·
    refine le_antisymm hNK fun k hk => ?_
    set Q₂ := ↥K ⧸ N₀
    have hQp : IsPGroup 2 Q₂ := by
      intro q
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective q
      have hk' : π k' ∈ N₀.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨n₀, hn₀, hn₀k⟩ := hk'
      have ho : n₀⁻¹ * k' ∈ CFSG.pCore 2 ↥K := by
        simp only [hπ, QuotientGroup.mk'_apply] at hn₀k
        exact QuotientGroup.eq.mp hn₀k
      obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, ho⟩
      refine ⟨a, ?_⟩
      have e : (QuotientGroup.mk k' : Q₂) = QuotientGroup.mk (n₀⁻¹ * k') := by
        rw [QuotientGroup.eq]
        have := hN₀n.conj_mem _ (N₀.inv_mem hn₀) k'⁻¹
        rwa [inv_inv, mul_assoc] at this
      rw [e, ← QuotientGroup.mk_pow]
      have : (n₀⁻¹ * k') ^ 2 ^ a = 1 := by
        have := congrArg Subtype.val ha
        simpa using this
      rw [this, QuotientGroup.mk_one]
    have : Group.IsNilpotent Q₂ := hQp.isNilpotent
    have hperfQ : commutator Q₂ = ⊤ := by
      rw [_root_.commutator_def, eq_top_iff]
      intro q _
      obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective q
      have hk' : k' ∈ commutator ↥K := hperfK ▸ Subgroup.mem_top _
      rw [_root_.commutator_def] at hk'
      have := Subgroup.mem_map_of_mem (QuotientGroup.mk' N₀) hk'
      rwa [Subgroup.map_commutator, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective _)] at this
    have h1 := eq_one_of_perfect_of_solvable hperfQ (QuotientGroup.mk (⟨k, hk⟩ : ↥K) : Q₂)
    rw [QuotientGroup.eq_one_iff, hN₀, Subgroup.mem_subgroupOf] at h1
    exact h1

end A6Gen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

theorem gen_of_cComp (hS : S.Hyp138) {H : Subgroup G} (hH : H ∈ S.Hz) {K : Subgroup G}
    (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hHK : H = K ⊔ (S.L1 ⊔ T))
    {X : Subgroup G} (hXH : X ≤ H) (hXQ : ¬ X ≤ pCoreOf 2 H)
    (hXR : X ≤ pCoreOf 2 (S.L1 ⊔ T)) : H = conjClosure X H ⊔ (S.L1 ⊔ T) := by
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF1 := (hS.hF H hH).toHypF91
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp hK
  have hLTH : S.L1 ⊔ T ≤ H := hF1.L₁T_le_H
  set R := pCoreOf 2 (S.L1 ⊔ T) with hR
  have hRp : IsPGroup 2 R := pCoreOf_isPGroup 2 _
  have hRn : S.L1 ⊔ T ≤ Subgroup.normalizer (R : Set G) := fun y hy =>
    le_normalizer_pCoreOf 2 _ hy
  have hOKp : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hOKn : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := by
    intro h hh
    have e : conjSub h (pCoreOf 2 K) = pCoreOf 2 K := by
      rw [← pCoreOf_conjSub, A6P.conjSub_eq_of_mem_normalizer (hKn hh)]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have := mul_mem_conjSub (g := h) hx
      rwa [e] at this
    · intro hx
      rw [← e, mem_conjSub] at hx
      simpa [mul_assoc] using hx
  have hnot : ¬ ⁅K, X⁆ ≤ pCoreOf 2 K := by
    intro hle
    apply hXQ
    set M := conjClosure X H with hM
    have hMH : M ≤ H := conjClosure_le fun h hh x hx => H.mul_mem (H.mul_mem hh (hXH hx))
      (H.inv_mem hh)
    have hLTK : S.L1 ⊔ T ≤ Subgroup.normalizer (K : Set G) := hLTH.trans hKn
    have hset := Subgroup.coe_mul_of_left_le_normalizer_right (S.L1 ⊔ T) K hLTK
    have hMO : M ≤ pCoreOf 2 K ⊔ R := by
      refine conjClosure_le fun h hh x hx => ?_
      have hh' : h ∈ ((S.L1 ⊔ T ⊔ K : Subgroup G) : Set G) := by
        rw [sup_comm]
        rw [← hHK]
        exact hh
      rw [hset] at hh'
      obtain ⟨y, hy, k, hk, rfl⟩ := hh'
      have hkx : ⁅k, x⁆ ∈ pCoreOf 2 K := hle (Subgroup.commutator_mem_commutator hk hx)
      have e : y * k * x * (y * k)⁻¹ = (y * ⁅k, x⁆ * y⁻¹) * (y * x * y⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
      · exact (Subgroup.mem_normalizer_iff.mp (hOKn (hLTH hy)) _).mp hkx
      · exact (Subgroup.mem_normalizer_iff.mp (hRn hy) x).mp (hXR hx)
    have hp : IsPGroup 2 ↥(pCoreOf 2 K ⊔ R) := by
      rw [sup_comm]
      exact IsPGroup.to_sup_of_normal_right' hRp hOKp ((pCoreOf_le 2 _).trans (hLTH.trans hOKn))
    have hMQ : M ≤ pCoreOf 2 H :=
      le_pCoreOf_of_le_normalizer hMH (le_normalizer_conjClosure X H) (hp.to_le hMO)
    exact (le_conjClosure X H).trans hMQ
  have hKX := A6Gen.comm_eq_of_not_le hq hperf (hXH.trans hKn) hnot
  have hKM : K ≤ conjClosure X H := by
    rw [← hKX, Subgroup.commutator_le]
    intro k hk x hx
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (mem_conjClosure (hKH hk) hx)
      (Subgroup.inv_mem _ (le_conjClosure X H hx))
  refine le_antisymm ?_ (sup_le (conjClosure_le fun h hh x hx =>
    H.mul_mem (H.mul_mem hh (hXH hx)) (H.inv_mem hh)) hLTH)
  calc H = K ⊔ (S.L1 ⊔ T) := hHK
    _ ≤ conjClosure X H ⊔ (S.L1 ⊔ T) := sup_le_sup_right hKM _

end Setting4

theorem lem13818Gen_holds
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V), S.Hyp138 →
      ∀ H ∈ S.Hz, ∀ K ∈ cComp H, H ≤ Subgroup.normalizer (K : Set G) → H = K ⊔ (S.L1 ⊔ T) →
        ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
          ∀ F : Subgroup G, F ≤ conjClosure S.V3 H → ¬ F ≤ F8.DH S.V3 (fsuV1 T V) H (g : G) →
            stab γ = conjClosure F (stab γ) ⊔ (stab γ ⊓ stab γ') := by
  intro G _ _ T L V S hS H hH K hK hKn hHK γ γ' g s F hFU hFD
  have hF := hS.hF H hH
  have hq := S.isQuasisimple_modO2 h36 h139 h1334 h13 hS hH hK
  have hstab : stab γ = conjSub (g : G) H := by
    rw [← s.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]
  have hstab' : stab γ' = conjSub (g : G) (L ⊔ T) := by
    rw [← s.edge₀, stab_smul, stab_γ₀ hF.amalgamHypV.le₁]
  have hinf : stab γ' ⊓ stab γ = conjSub (g : G) (S.L1 ⊔ T) := by
    rw [hstab, hstab', ← conjSub_inf, hF.toHypF91.LT_inf_H]
    rfl
  set X := conjSub (g : G)⁻¹ F with hX
  have hFX : conjSub (g : G) X = F := by
    rw [hX]
    have := conjSub_conjSub_inv ((g : G)⁻¹) F
    rwa [inv_inv] at this
  have hUP : conjClosure S.V3 H ≤ pCoreOf 2 (stab γ' ⊓ stab γ) :=
    (conjClosure_mono S.V3_le_V le_rfl).trans (hF.F913_2 s).1
  have hXR : X ≤ pCoreOf 2 (S.L1 ⊔ T) := by
    rw [hX, conjSub_le_iff, inv_inv, ← pCoreOf_conjSub, ← hinf]
    exact hFU.trans hUP
  have hXH : X ≤ H := hXR.trans ((pCoreOf_le 2 _).trans hF.toHypF91.L₁T_le_H)
  have hXQ : ¬ X ≤ pCoreOf 2 H := by
    intro hle
    apply hFD
    have hFO : F ≤ pCoreOf 2 (stab γ) := by
      rw [hstab, pCoreOf_conjSub, ← hFX]
      exact conjSub_mono _ hle
    rw [hF.pCoreOf_stab_eq_centralizerMod s] at hFO
    intro f hf
    obtain ⟨-, hfN, hfc⟩ := hFO hf
    exact ⟨hFU hf, hfN, hfc⟩
  have hgen := S.gen_of_cComp hS hH hK hq hKn hHK hXH hXQ hXR
  have h2 := congrArg (conjSub (g : G)) hgen
  rw [conjSub_sup, conjSub_conjClosure_eq, hFX, ← hstab, ← hinf, inf_comm] at h2
  exact h2

theorem lem13818Four_holds
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two) :
    Lem13818Four := by
  intro G _ _ T L V S hS H hH K hK hKn hHK hnt γ γ' g s hDγ hDH hle
  have hF := hS.hF H hH
  have hF1 := hF.toHypF91
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hS H hH K hK hKn hHK γ γ' g s
    (conjClosure S.V3 H) le_rfl (fun h => hDH.ne (le_antisymm hDH.le h))
  by_cases hD : ⁅conjClosure S.V3 H, F8.Dγ S.V3 (fsuV1 T V) H (g : G)⁆ = ⊥
  swap
  · exact S.lemma13_8_11_two hS.hNS h13315 h1356two hH hF h13314 s hDγ hgen hle hDH hD
  set Q := pCoreOf 2 H with hQ
  set U := F8.Uγ S.V3 H (g : G) with hUdef
  set W := F8.Uγ V H (g : G) with hWdef
  have hUW : U ≤ W := hF.Uγ_le_Vγ
  have hU2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hF.isElemAbelian_Uγ
  have hW2 : IsPGroup 2 W := isPGroup_of_isElemAbelian hF.isElemAbelian_Vγ
  have hDQ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) = U ⊓ Q := hF.Dγ_eq_inf_pCoreOf s
  have iU : (U ⊓ Q).relIndex U = 2 ^ mIdx U (U ⊓ Q) := HypF98.relIndex_eq_two_pow_mIdx hU2
  have iW : (W ⊓ Q).relIndex W = 2 ^ mIdx W (W ⊓ Q) := HypF98.relIndex_eq_two_pow_mIdx hW2
  rw [Subgroup.inf_relIndex_left] at iU iW
  have hmono : mIdx U (U ⊓ Q) ≤ mIdx W (W ⊓ Q) := by
    have h1 := Subgroup.relIndex_le_of_le_right hUW (relIndex_ne_zero' Q W)
    rw [iU, iW] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have hmU : mIdx U (U ⊓ Q) ≠ 0 := by
    intro h0
    rw [h0, pow_zero, Subgroup.relIndex_eq_one] at iU
    rw [hDQ] at hDγ
    exact hDγ.ne (le_antisymm inf_le_left (le_inf le_rfl iU))
  by_cases h2 : 2 ≤ mIdx U (U ⊓ Q)
  · omega
  exfalso
  have hm1 : mIdx U (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by rw [hDQ]; omega
  obtain ⟨δ, δ', k, y, sk, -, -, hUδ, hUHy, hDHk, hDγk⟩ :=
    hF.exists_symmetric_setup s (hF.not_Vγ_le_ballStab_of_lt s hDγ)
  have hUδH : F8.Uγ S.V3 H (k : G) ≤ H := hF.Uγ_le_H sk
  have hDγk' : F8.Dγ S.V3 (fsuV1 T V) H (k : G) < F8.Uγ S.V3 H (k : G) := by
    rw [hDγk, hUδ]
    exact lt_of_le_of_ne (conjSub_mono _ hDH.le) fun e => hDH.ne ((conjSub_inj _).1 e)
  obtain ⟨x, hxU, hxD⟩ := IsConcreteLE.exists_of_lt hDγk'
  have hxH : x ∈ H := hUδH hxU
  have hxc : ∀ u ∈ F8.DH S.V3 (fsuV1 T V) H (k : G), x * u = u * x := by
    intro u hu
    rw [hDHk, mem_conjSub] at hu
    rw [hUδ, mem_conjSub] at hxU
    have h1 := Subgroup.commutator_mem_commutator hxU hu
    rw [hD, Subgroup.mem_bot, commutatorElement_def] at h1
    have e : x * u = (y : G) * ((((y : G)⁻¹ * x * y) * ((y : G)⁻¹ * u * y) *
        ((y : G)⁻¹ * x * y)⁻¹ * ((y : G)⁻¹ * u * y)⁻¹) * (((y : G)⁻¹ * u * y) *
        ((y : G)⁻¹ * x * y))) * (y : G)⁻¹ := by group
    rw [e, h1, one_mul]
    group
  have hUH2 : IsPGroup 2 (conjClosure S.V3 H) :=
    (pCoreOf_isPGroup 2 H).to_le hF1.conjClosure_Vp_le_pCoreOf
  have hidx : (F8.DH S.V3 (fsuV1 T V) H (k : G)).relIndex (conjClosure S.V3 H) = 2 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hUH2, ← hUHy, hDHk, F9.mIdx_conjSub, hm1, pow_one]
  have hidx' : ((F8.DH S.V3 (fsuV1 T V) H (k : G)).subgroupOf (conjClosure S.V3 H)).index = 2 :=
    hidx
  have hDHlt : F8.DH S.V3 (fsuV1 T V) H (k : G) < conjClosure S.V3 H := by
    refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun e => ?_
    rw [e, Subgroup.relIndex_self] at hidx
    exact absurd hidx (by norm_num)
  obtain ⟨u₀, hu₀U, hu₀D⟩ := IsConcreteLE.exists_of_lt hDHlt
  refine hnt x hxH ⟨fun hall => hxD ⟨hxU, hF1.H_normalizes_V₁ hxH, hall⟩,
    x * u₀ * x⁻¹ * u₀⁻¹, fun u hu => ?_⟩
  by_cases huD : u ∈ F8.DH S.V3 (fsuV1 T V) H (k : G)
  · left
    rw [hxc u huD, mul_inv_cancel_right, mul_inv_cancel]
    exact (fsuV1 T V).one_mem
  · right
    have hd : u₀⁻¹ * u ∈ F8.DH S.V3 (fsuV1 T V) H (k : G) := by
      have h1 := (Subgroup.mul_mem_iff_of_index_two hidx'
        (a := (⟨u₀, hu₀U⟩ : ↥(conjClosure S.V3 H))⁻¹) (b := ⟨u, hu⟩)).2
        ⟨fun h => absurd (by simpa using (Subgroup.mem_subgroupOf.1 h)) (fun h' => hu₀D
          (by simpa using (F8.DH S.V3 (fsuV1 T V) H (k : G)).inv_mem h')),
          fun h => absurd (Subgroup.mem_subgroupOf.1 h) huD⟩
      simpa using Subgroup.mem_subgroupOf.1 h1
    have hcd := hxc _ hd
    have e : x * u * x⁻¹ * u⁻¹ * (x * u₀ * x⁻¹ * u₀⁻¹)⁻¹ =
        (x * u₀ * x⁻¹) * ((x * (u₀⁻¹ * u)) * x⁻¹ * (u₀⁻¹ * u)⁻¹) * (x * u₀ * x⁻¹)⁻¹ := by
      group
    rw [e, hcd]
    convert (fsuV1 T V).one_mem using 1
    group

end CFSG.Quasithin.H13.A6
