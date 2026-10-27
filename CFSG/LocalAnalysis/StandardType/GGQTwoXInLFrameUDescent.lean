module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDescentR
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLAmbDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLQuot
public import CFSG.LocalAnalysis.StandardType.GGXInLDispatch
public import CFSG.LocalAnalysis.StandardType.GGTCJDescent
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviCount
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggQTwoXInLU_descent
    (hS : GGQTwoSetting 3 B Bs x L D J) (hxL : x ∈ L)
    (hA : GGQTwoXInLAmbOn (fun t => t = .twA) Bs (ggG0 3 B x L D J)) :
    ∃ (N : ℕ) (K : Type) (_ : Field K) (_ : Finite K),
      Nonempty (GGXInL.lup8f_UnitaryMarking Bs (ggG0 3 B x L D J) N K) ∧ 7 ≤ N := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hx3 : x ^ 3 = 1 := hcfg.2.1.2.1.2 x hxBs
  have hX : x ∈ ggG0 3 B x L D J := le_ggG0_left 3 B x L D J hxL
  let X := ggG0 3 B x L D J
  unfold GGQTwoXInLAmbOn at hA
  obtain ⟨hperfX, labH, hLamH, hrawH⟩ := hA
  obtain ⟨R0, hR0grp, I0, F0, hQ0⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hrawH
  obtain ⟨-, -, -, htagH, -, -⟩ := hQ0
  rcases labH with ⟨tag, rank, n⟩
  subst htagH
  dsimp only [LargeEvenRawDatum, LargeEvenRecipeUnitary] at hrawH
  obtain ⟨K, hKfield, hKfin, hKcard, hQ'⟩ := hrawH
  obtain ⟨hsimple, hnonab, θ, htagCond, hnorm, hact⟩ := hQ'
  let R := LargeEvenProj (LargeEvenSUGroup (Fin (rank + 1)) K (2 ^ n))
  have hL : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hcfg.1.2.2.2.2.2.2.1.2.2.2.1
  have hLX : L ≤ X := le_ggG0_left 3 B x L D J
  have hcompX : IsComponentOf L (Subgroup.centralizer ({x} : Set G) ⊓ X) :=
    ggIsComponentOf_inf_of_le hL hLX
  have hJsub : IsComponentOf (L.subgroupOf X) ((Subgroup.centralizer ({x} : Set G) ⊓ X).subgroupOf X) :=
    ggIsComponentOf_subgroupOf_of_le X hLX hcompX
  let xX : ↥X := ⟨x, hX⟩
  let e : MulAut ↥X := MulAut.conj (xX⁻¹)
  have hcent : ((Subgroup.centralizer ({x} : Set G) ⊓ X).subgroupOf X) = ggFixSub e := by
    ext l
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      mem_ggFixSub, e, MulAut.conj_apply]
    constructor
    · rintro ⟨h, -⟩
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, xX, inv_inv]
      rw [mul_assoc, h]
      group
    · intro h
      constructor
      · have h0 : ((xX⁻¹ * l * xX⁻¹⁻¹ : ↥X) : G) = (l : G) := congrArg Subtype.val h
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, xX, inv_inv] at h0
        have h1 : x⁻¹ * (l : G) * x = (l : G) := by
          simpa [xX, inv_inv] using h0
        calc ↑l * x = x * (x⁻¹ * ↑l * x) := by group
          _ = x * ↑l := by rw [h1]
      · exact l.2
  have hJ : IsComponentOf (L.subgroupOf X) (ggFixSub e) := by
    rwa [← hcent]
  obtain ⟨u, huI, huact⟩ := hact x hxBs
  let ψ : ↥X →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hker : ψ.ker ≤ Subgroup.center ↥X := by
    intro l hl
    simp only [ψ, MonoidHom.mem_ker, MonoidHom.comp_apply] at hl
    have h1 : QuotientGroup.mk' (Subgroup.center ↥X) l = 1 := θ.injective (by simpa using hl)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφ : ∀ l : ↥X, u (ψ l) = ψ (e l) := by
    intro l
    have h := huact l (e l) (by
      simp only [e, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv, xX, inv_inv])
    simpa [ψ, e, xX] using h
  obtain ⟨hJ'map, ⟨eJ⟩⟩ := TCJ.ggTCJ_descent ψ hψ hker e u hφ (L.subgroupOf X) hJ
  have hxX3 : (xX : ↥X) ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow]
    exact hx3
  have he3 : e ^ 3 = 1 := by
    dsimp only [e]
    rw [← map_pow, inv_pow, hxX3, inv_one]
    ext g
    simp only [MulAut.conj_apply, MulAut.one_apply, one_mul, mul_one, inv_one]
  have hu3 : u ^ 3 = 1 := by
    ext r
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    have h1 : u (θ (QuotientGroup.mk' (Subgroup.center ↥X) l)) =
        θ (QuotientGroup.mk' (Subgroup.center ↥X) (e l)) := by
      apply huact l (e l)
      dsimp only [e, MulAut.conj_apply, xX]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    have h2 : u (θ (QuotientGroup.mk' (Subgroup.center ↥X) (e l))) =
        θ (QuotientGroup.mk' (Subgroup.center ↥X) (e (e l))) := by
      apply huact (e l) (e (e l))
      dsimp only [e, MulAut.conj_apply, xX]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    have h3 : u (θ (QuotientGroup.mk' (Subgroup.center ↥X) (e (e l)))) =
        θ (QuotientGroup.mk' (Subgroup.center ↥X) (e (e (e l)))) := by
      apply huact (e (e l)) (e (e (e l)))
      dsimp only [e, MulAut.conj_apply, xX]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    have h4 : e (e (e l)) = l := by
      have h := congrArg (fun f => f l) he3
      simp only [MulAut.one_apply] at h
      change e (e (e l)) = l
      exact h
    calc (u ^ 3) (θ (QuotientGroup.mk' (Subgroup.center ↥X) l))
        = u (u (u (θ (QuotientGroup.mk' (Subgroup.center ↥X) l)))) := rfl
      _ = u (u (θ (QuotientGroup.mk' (Subgroup.center ↥X) (e l)))) := by rw [h1]
      _ = u (θ (QuotientGroup.mk' (Subgroup.center ↥X) (e (e l)))) := by rw [h2]
      _ = θ (QuotientGroup.mk' (Subgroup.center ↥X) (e (e (e l)))) := by rw [h3]
      _ = θ (QuotientGroup.mk' (Subgroup.center ↥X) l) := by rw [h4]
  have hu1 : u ≠ 1 := by
    intro hu
    have hge : ggInducedAut θ e = 1 := by
      ext r
      obtain ⟨q, rfl⟩ := θ.surjective r
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
      have h1 : θ (QuotientGroup.mk' (Subgroup.center ↥X) (e l)) =
          u (θ (QuotientGroup.mk' (Subgroup.center ↥X) l)) := by
        apply (huact l (e l) _).symm
        dsimp only [e, MulAut.conj_apply, xX]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      simp only [hu, MulAut.one_apply] at h1
      rw [ggInducedAut_apply]
      exact h1
    have he : e = 1 := ggInducedAut_injective_of_perfect hperfX θ (by simpa using hge)
    have hxcent : x ∈ Subgroup.centralizer (X : Set G) := by
      intro y hy
      have h2 : (xX⁻¹ * (⟨y, hy⟩ : ↥X) * xX⁻¹⁻¹ : ↥X) = ⟨y, hy⟩ := by
        have h := congrArg (fun f => f ⟨y, hy⟩) he
        simp only [MulAut.one_apply] at h
        exact h
      have h3 : ((xX⁻¹ * (⟨y, hy⟩ : ↥X) * xX⁻¹⁻¹ : ↥X) : G) = y := congrArg Subtype.val h2
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, xX, inv_inv] at h3
      calc y * x = x * (x⁻¹ * y * x) := by group
        _ = x * y := by rw [h3]
    obtain ⟨y, K, hnb⟩ := exists_ggNbr hcfg.1.2.2.2.2.2.2.2 hcfg.2.2
    have hKX : K ≤ X := le_ggG0_of_ggNbr hnb
    have hxK : x ∈ Subgroup.centralizer (K : Set G) := by
      intro k hk
      exact hxcent k (hKX hk)
    exact ggNbr_x_not_mem_centralizer hnb hxK
  obtain ⟨hp3, hcases⟩ := CFSG.StandardType.GGXInL.lup8g_dispatch hS hxL
  clear hp3
  let e_sub : ↥(L.subgroupOf X) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLX
  let e_quot : (↥(L.subgroupOf X) ⧸ Subgroup.center ↥(L.subgroupOf X)) ≃*
      (↥L ⧸ Subgroup.center ↥L) :=
    QuotientGroup.congr _ _ e_sub (Subgroup.map_center_eq e_sub)
  have hJlabOf : ∀ lab : LargeEvenLabel, GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) →
      GGHasLabel lab (↥((L.subgroupOf X).map ψ) ⧸ Subgroup.center ↥((L.subgroupOf X).map ψ)) :=
    fun lab h => ggHasLabel_of_mulEquiv eJ (ggHasLabel_of_mulEquiv e_quot.symm h)
  dsimp only [LargeEvenInLambda2] at hLamH
  have hN3 : 3 ≤ rank + 1 := by
    have h2 : 2 ≤ rank := hLamH.2.1
    exact Nat.succ_le_succ h2
  have hNq : (rank + 1, 2 ^ n) ≠ (3, 2) := by
    intro h
    have h1 : rank + 1 = 3 := (Prod.ext_iff.mp h).1
    have h2 : 2 ^ n = 2 := (Prod.ext_iff.mp h).2
    have hn1 : n = 1 := Nat.pow_right_injective (a := 2) (by norm_num) (by simpa using h2)
    have h3 : rank = 2 := by omega
    have h4 : 2 ≤ n := hLamH.2.2 h3
    omega
  have hJ_open : CFSG.Open.IsComponentOf ((L.subgroupOf X).map ψ) (ggAutFixedSubgroup u) := by
    rw [← isComponentOf_iff_open]
    exact hJ'map
  rcases hcases with hunitary | htwE6
  ·
    obtain ⟨nL, K', hKfield', hKfin', ⟨M⟩, h3n, h6n⟩ := hunitary
    let lab : LargeEvenLabel := ⟨.twA, nL - 1, 1⟩
    have hE : Nat.card K' = (2 ^ 1) ^ 2 := by
      rw [M.card_K]
      norm_num
    have hpos : 0 < nL := Nat.lt_of_lt_of_le (by norm_num) h6n
    have hn1 : nL - 1 + 1 = nL := Nat.succ_pred_eq_of_pos hpos
    have hlabL : GGHasLabel lab (↥L ⧸ Subgroup.center ↥L) := by
      dsimp only [GGHasLabel, lab, LargeEvenRawDatum, LargeEvenRecipeUnitary]
      rw [hn1]
      exact ⟨K', hKfield', hKfin', hE, ⟨M.theta⟩⟩
    have hLambda : LargeEvenInLambda2 lab := by
      dsimp only [lab, LargeEvenInLambda2]
      refine ⟨by norm_num, by omega, ?_⟩
      intro h
      omega
    have htag : lab.tag = .twE6 ∨ (lab.tag = .twA ∧ 5 ≤ lab.rank) := by
      right
      refine ⟨rfl, ?_⟩
      show 5 ≤ nL - 1
      omega
    have hbox := ggQTwoXInLU_descentR (N := rank + 1) (m := n) (K := K)
      hKcard hN3 hNq huI hu3 hu1 hJ_open hLambda rfl htag (hJlabOf lab hlabL)
    obtain ⟨hm, -, hNbound⟩ := hbox
    dsimp only at θ hKcard hact
    subst n
    refine ⟨rank + 1, K, hKfield, hKfin, ?_, ?_⟩
    · refine ⟨{
        theta := θ
        card_K := by rw [hKcard]; norm_num
        normalizes := hnorm
        action := hact
      }⟩
    · have h5 : 5 ≤ lab.rank := by
        show 5 ≤ nL - 1
        omega
      omega
  ·
    exfalso
    obtain ⟨-, lab₁, hΛ₁, hraw₁⟩ := htwE6
    obtain ⟨-, lab₂, hΛ₂, hraw₂⟩ := hS.2.1
    obtain ⟨-, -, -, -, -, -, -, htag₁, -, -⟩ := largeEvenRawDatum_exists hraw₁
    obtain ⟨-, -, -, -, -, -, -, hn₂, -, -⟩ := largeEvenRawDatum_exists hraw₂
    have hl₁ : GGHasLabel lab₁ (↥L ⧸ Subgroup.center ↥L) := by
      unfold GGHasLabel
      refine largeEvenRawDatum_mono ?_ hraw₁
      rintro R' _ I' F' ⟨-, -, θ', -⟩
      exact ⟨θ'⟩
    have hl₂ : GGHasLabel lab₂ (↥L ⧸ Subgroup.center ↥L) := by
      unfold GGHasLabel
      refine largeEvenRawDatum_mono ?_ hraw₂
      rintro R' _ I' F' ⟨-, -, θ', -⟩
      exact ⟨θ'⟩
    have h12 : lab₂ = lab₁ := by
      rcases ggLabelRigidInput_holds lab₁ lab₂ _ hΛ₁ hΛ₂ hl₁ hl₂ with
        h | ⟨hb, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨-, h1⟩
      · exact h.symm
      · rcases hb with hb | hb <;> rw [htag₁] at hb <;> cases hb
      all_goals
        have ht := congrArg LargeEvenLabel.tag h1
        rw [htag₁] at ht
        cases ht
    have hn₁ : lab₁.n = 1 := by
      have h1 : 1 ≤ lab₁.n := hΛ₁.1
      have h2 : lab₂.n < 2 := hn₂
      rw [h12] at h2
      omega
    have hbox := ggQTwoXInLU_descentR (N := rank + 1) (m := n) (K := K)
      hKcard hN3 hNq huI hu3 hu1 hJ_open hΛ₁ hn₁ (Or.inl htag₁) (hJlabOf lab₁ hl₁)
    have ht := hbox.2.1
    rw [htag₁] at ht
    cases ht

end CFSG.StandardType

end
