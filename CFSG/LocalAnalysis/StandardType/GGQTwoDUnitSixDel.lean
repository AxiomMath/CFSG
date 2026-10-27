module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitSixBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitAnchor
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitDeleteStdA
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMLin
import CFSG.LocalAnalysis.StandardType.GGNbrBalanceBasic
import CFSG.Foundations.QuasisimpleMulEquiv
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.LocalAnalysis.StandardType.GGQTwoDTransport

public section

namespace CFSG.StandardType.NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.exists_chart_of_img (hD : Datum p N f L Bs Z) {J : Subgroup G} (hJL : J ≤ L)
    (hJZ : ∀ j ∈ J, j ∈ Z → j = 1) {H : Type} [Group H] (φ : H →* Q)
    (hφ : Function.Injective φ) (hJ : img N f J = φ.range) :
    ∃ θ : H →* G, Function.Injective θ ∧ θ.range = J ∧
      ∀ h : H, ∃ hN : θ h ∈ N, f ⟨θ h, hN⟩ = φ h := by
  have hJN : J ≤ N := hJL.trans hD.LN
  let ρ : ↥J →* Q := f.comp (Subgroup.inclusion hJN)
  have hρ : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro j hj
    have hk : Subgroup.inclusion hJN j ∈ f.ker := hj
    have hZ : (j : G) ∈ Z := by simpa using (hD.mem_ker_iff _).1 hk
    exact Subtype.ext (hJZ j j.2 hZ)
  have hρr : ρ.range = φ.range := by
    rw [← hJ]
    ext q
    constructor
    · rintro ⟨j, rfl⟩
      exact mem_img.2 ⟨Subgroup.inclusion hJN j, j.2, rfl⟩
    · intro hq
      obtain ⟨u, huJ, rfl⟩ := mem_img.1 hq
      exact ⟨⟨u, huJ⟩, rfl⟩
  let e : H ≃* ↥J := (MonoidHom.ofInjective hφ).trans
    ((MulEquiv.subgroupCongr hρr.symm).trans (MonoidHom.ofInjective hρ).symm)
  refine ⟨J.subtype.comp e.toMonoidHom, J.subtype_injective.comp e.injective, ?_,
    fun h => ⟨hJN (e h).2, ?_⟩⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  · have h1 : ((MonoidHom.ofInjective hρ (e h) : ↥ρ.range) : Q) = φ h := by
      simp only [e, MulEquiv.trans_apply, MulEquiv.apply_symm_apply,
        MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
    rw [MonoidHom.ofInjective_apply] at h1
    exact h1

end CFSG.StandardType.NsQuot

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary CFSG.ClassicalGroups.Unitary.SUThreeTwoDiag

variable {G : Type} [Group G] [Finite G] {p : ℕ} {N L Bs Z : Subgroup G}
variable {K : Type} [Field K] [Finite K] [CharP K 2] {Q : Type} [Group Q]
variable {f : ↥N →* Q} {ψ : Su K 2 1 6 →* Q}

theorem ggQTwoDUnitSix_chart (hK : Nat.card K = 4) (hD : NsQuot.Datum p N f L Bs Z)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6)) (T : Finset (Fin 6)) (hT : T.card < 6)
    {J : Subgroup G} (hJL : J ≤ L) (hJZ : ∀ j ∈ J, j ∈ Z → j = 1)
    (hJ : NsQuot.img N f J = (coordBlockSU K 2 1 T).map ψ) :
    ∃ θ : Su K 2 1 T.card →* G, Function.Injective θ ∧ θ.range = J ∧
      ∀ X, ∃ hN : θ X ∈ N, f ⟨θ X, hN⟩ = ψ (blockSUOn K 2 1 T X) := by
  have hS := ggQTwoDUnit_injective_coordBlockSU hK ψ hψk (by norm_num) hT
  have hinj : Function.Injective (ψ.comp (blockSUOn K 2 1 T)) := by
    intro X Y hXY
    apply blockSUOn_injective (K := K) (p := 2) (f := 1) T
    have hX : blockSUOn K 2 1 T X ∈ coordBlockSU K 2 1 T := ⟨X, rfl⟩
    have hY : blockSUOn K 2 1 T Y ∈ coordBlockSU K 2 1 T := ⟨Y, rfl⟩
    exact congrArg Subtype.val (hS (a₁ := ⟨_, hX⟩) (a₂ := ⟨_, hY⟩) hXY)
  have hrange : (ψ.comp (blockSUOn K 2 1 T)).range = (coordBlockSU K 2 1 T).map ψ :=
    MonoidHom.range_comp _ _
  exact hD.exists_chart_of_img hJL hJZ _ hinj (hJ.trans hrange.symm)

theorem ggQTwoDUnitSix_chart_conj (hK : Nat.card K = 4) (hD : NsQuot.Datum p N f L Bs Z)
    (T : Finset (Fin 6)) {J : Subgroup G} (hJL : J ≤ L) [Group.IsPerfect ↥J]
    (hJZ : ∀ j ∈ J, j ∈ Z → j = 1)
    (hJ : NsQuot.img N f J = (coordBlockSU K 2 1 T).map ψ)
    {θ : Su K 2 1 T.card →* G} (hθr : θ.range = J)
    (hθf : ∀ X, ∃ hN : θ X ∈ N, f ⟨θ X, hN⟩ = ψ (blockSUOn K 2 1 T X))
    {s : ↥N} (hsL : ∀ l ∈ L, (s : G) * l * (s : G)⁻¹ ∈ L) {u : Fin 6 → Kˣ}
    (hs : qTwoChartTwoThree_induces ψ (f s) u) (X : Su K 2 1 T.card) :
    (s : G) * θ X * (s : G)⁻¹ =
      θ (dconjSu hK (fun k => u (T.equivFin.symm k)) X) := by
  have himg : ∀ Y : Su K 2 1 T.card,
      f s * ψ (blockSUOn K 2 1 T Y) * (f s)⁻¹ =
        ψ (blockSUOn K 2 1 T
          (dconjSu hK (fun k => u (T.equivFin.symm k)) Y)) := by
    intro Y
    obtain ⟨u', hu', hψu'⟩ := hs (blockSUOn K 2 1 T Y)
    have hu'eq : u' = blockSUOn K 2 1 T
        (dconjSu hK (fun k => u (T.equivFin.symm k)) Y) :=
      Subtype.ext (by
        rw [hu', ggQTwoDUnit_coe_blockSUOn_dconjSu hK T
          (g := qTwoChartTwoThree_diag u) rfl Y])
    rw [← hψu', hu'eq]
  have hnorm : ∀ j ∈ J, (s : G) * j * (s : G)⁻¹ ∈ J := by
    refine hD.conj_mem_of_img hJL s hsL fun q hq => ?_
    rw [hJ] at hq ⊢
    obtain ⟨w, ⟨Y, rfl⟩, rfl⟩ := hq
    rw [himg]
    exact ⟨_, ⟨_, rfl⟩, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X', X' = dconjSu hK (fun k => u (T.equivFin.symm k)) X :=
    ⟨_, rfl⟩
  rw [← hX']
  have hθX : θ X ∈ J := by rw [← hθr]; exact ⟨X, rfl⟩
  have hθX' : θ X' ∈ J := by rw [← hθr]; exact ⟨X', rfl⟩
  have hy : (s : G) * θ X * (s : G)⁻¹ ∈ J := hnorm _ hθX
  obtain ⟨hN, hfX⟩ := hθf X
  obtain ⟨hN', hfX'⟩ := hθf X'
  have hmemN : (s : G) * θ X * (s : G)⁻¹ * (θ X')⁻¹ ∈ N :=
    N.mul_mem (N.mul_mem (N.mul_mem s.2 hN) (N.inv_mem s.2)) (N.inv_mem hN')
  have hker : (⟨(s : G) * θ X * (s : G)⁻¹ * (θ X')⁻¹, hmemN⟩ : ↥N) ∈ f.ker := by
    have heq : (⟨(s : G) * θ X * (s : G)⁻¹ * (θ X')⁻¹, hmemN⟩ : ↥N) =
        s * ⟨θ X, hN⟩ * s⁻¹ * (⟨θ X', hN'⟩ : ↥N)⁻¹ := rfl
    rw [heq, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hfX, hfX', himg,
      ← hX', mul_inv_cancel]
  have hZ : (s : G) * θ X * (s : G)⁻¹ * (θ X')⁻¹ ∈ Z := (hD.mem_ker_iff _).1 hker
  have h1 := hJZ _ (J.mul_mem hy (J.inv_mem hθX')) hZ
  exact mul_inv_eq_one.mp h1

theorem ggQTwoDUnitSix_chart_commute (hK : Nat.card K = 4) (hD : NsQuot.Datum p N f L Bs Z)
    (T : Finset (Fin 6)) {J : Subgroup G} (hJL : J ≤ L) [Group.IsPerfect ↥J]
    (hJZ : ∀ j ∈ J, j ∈ Z → j = 1)
    (hJ : NsQuot.img N f J = (coordBlockSU K 2 1 T).map ψ)
    {θ : Su K 2 1 T.card →* G} (hθr : θ.range = J)
    (hθf : ∀ X, ∃ hN : θ X ∈ N, f ⟨θ X, hN⟩ = ψ (blockSUOn K 2 1 T X))
    {s : ↥N} (hsL : ∀ l ∈ L, (s : G) * l * (s : G)⁻¹ ∈ L) {u : Fin 6 → Kˣ}
    (hs : qTwoChartTwoThree_induces ψ (f s) u) (hu : ∀ i ∈ T, u i = 1) :
    ∀ j ∈ J, (s : G) * j = j * (s : G) := by
  intro j hj
  rw [← hθr] at hj
  obtain ⟨X, rfl⟩ := hj
  have h1 : (fun k => u (T.equivFin.symm k)) = 1 := by
    funext k
    exact hu _ (T.equivFin.symm k).2
  have hd1 : (CFSG.LieType.Steinberg.diagGL
      (1 : Fin T.card → Kˣ) : GL (Fin T.card) K) = 1 := by
    apply Units.ext
    rw [CFSG.LieType.Steinberg.coe_diagGL]
    simp
  have h2 : dconjSu hK (fun k => u (T.equivFin.symm k)) X = X := by
    apply Subtype.ext
    rw [coe_dconjSu, h1, hd1, inv_one, one_mul, mul_one]
  have h := ggQTwoDUnitSix_chart_conj hK hD T hJL hJZ hJ hθr hθf hsL hs X
  rw [h2] at h
  calc (s : G) * θ X = (s : G) * θ X * (s : G)⁻¹ * (s : G) := by group
    _ = θ X * (s : G) := by rw [h]

omit [Finite G] in
theorem ggQTwoDUnitSix_J_quasisimple (hK : Nat.card K = 4) (T : Finset (Fin 6))
    (hT : 4 ≤ T.card) {J : Subgroup G} {θ : Su K 2 1 T.card →* G} (hθ : Function.Injective θ)
    (hθr : θ.range = J) : CFSG.Assembly.IsQuasisimple ↥J := by
  have hq : CFSG.IsQuasisimple (Su K 2 1 T.card) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine CFSG.GH74.L5U5.isQuasisimple_su (K := K) (p := 2) (f := 1) ?_ ?_ ?_
    · rw [hK]; norm_num
    · omega
    · intro h
      exact absurd (Prod.mk.inj h).1 (by omega)
  let e : ↥J ≃* Su K 2 1 T.card :=
    (MulEquiv.subgroupCongr hθr.symm).trans (MonoidHom.ofInjective hθ).symm
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
    (hq.of_mulEquiv e)

theorem ggQTwoDUnitSix_J_comp_L (hK : Nat.card K = 4) (hD : NsQuot.Datum p N f L Bs Z)
    (hψr : ψ.range = NsQuot.img N f L) (c : Fin 6) {J : Subgroup G} (hJL : J ≤ L)
    [Group.IsPerfect ↥J] (hJZ : ∀ j ∈ J, j ∈ Z → j = 1)
    (hJ : NsQuot.img N f J = (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    {θ : Su K 2 1 (Finset.univ.erase c).card →* G} (hθ : Function.Injective θ)
    (hθr : θ.range = J)
    (hθf : ∀ X, ∃ hN : θ X ∈ N, f ⟨θ X, hN⟩ = ψ (blockSUOn K 2 1 (Finset.univ.erase c) X))
    {b' : ↥N} (hb'L : ∀ l ∈ L, (b' : G) * l * (b' : G)⁻¹ ∈ L) {ω : Kˣ} (hω : orderOf ω = 3)
    (hb' : qTwoChartTwoThree_induces ψ (f b') (qtwoDB39_delDiag ω c)) :
    CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer ({(b' : G)} : Set G)) := by
  have hω1 : ω ≠ 1 := by
    rintro rfl
    simp at hω
  have hcomm := ggQTwoDUnitSix_chart_commute hK hD (Finset.univ.erase c) hJL hJZ hJ hθr hθf hb'L
    hb' (fun i hi => by simp [qtwoDB39_delDiag, (Finset.mem_erase.mp hi).1])
  have hJA : J ≤ L ⊓ Subgroup.centralizer ({(b' : G)} : Set G) := fun j hj =>
    Subgroup.mem_inf.mpr ⟨hJL hj, Subgroup.mem_centralizer_singleton_iff.mpr (hcomm j hj).symm⟩
  have hnorm : ∀ l ∈ L ⊓ Subgroup.centralizer ({(b' : G)} : Set G), ∀ j ∈ J,
      l * j * l⁻¹ ∈ J := by
    intro l hl
    obtain ⟨hlL, hlC⟩ := Subgroup.mem_inf.mp hl
    have hlN : l ∈ N := hD.LN hlL
    obtain ⟨w, hw⟩ : f ⟨l, hlN⟩ ∈ ψ.range := by
      rw [hψr]
      exact NsQuot.mem_img.2 ⟨⟨l, hlN⟩, hlL, rfl⟩
    have hlb : (⟨l, hlN⟩ : ↥N) * b' = b' * ⟨l, hlN⟩ :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hlC)
    obtain ⟨w', hw'mat, hψw'⟩ := hb' w
    have hψeq : ψ w' = ψ w := by
      rw [hψw', hw, ← map_mul, ← map_inv, ← map_mul, ← hlb, mul_inv_cancel_right]
    have hz : w' * w⁻¹ ∈ Subgroup.center (Su K 2 1 6) :=
      hψk (by rw [MonoidHom.mem_ker, map_mul, map_inv, hψeq, mul_inv_cancel])
    have hconj : qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c) w = (w' * w⁻¹) * w := by
      rw [inv_mul_cancel_right]
      exact Subtype.ext (by rw [qtwoDB39_conjAut_apply, hw'mat])
    have hfix := qtwoDB39_fixed_of_conj_scalar hK (by norm_num) hω hz hconj
    have hwfix : w ∈ CFSG.ClassicalInvolution.Balance.fixedGroup
        (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c)) := hfix
    have hblock : ∀ v ∈ coordBlockSU K 2 1 (Finset.univ.erase c),
        w * v * w⁻¹ ∈ coordBlockSU K 2 1 (Finset.univ.erase c) := by
      intro v hv
      have hvF : v ∈ CFSG.ClassicalInvolution.Balance.fixedGroup
          (qtwoDB39_conjAut hK (qtwoDB39_delDiag ω c)) :=
        qtwoDB39_coordBlock_le_fixed hK (fun i hi j hj => by
          simp [qtwoDB39_delDiag, (Finset.mem_erase.mp hi).1, (Finset.mem_erase.mp hj).1]) hv
      have hN := (qtwoDB39_coordBlock_normal (c := c) hK hω1).conj_mem ⟨v, hvF⟩
        (Subgroup.mem_subgroupOf.mpr hv) ⟨w, hwfix⟩
      exact Subgroup.mem_subgroupOf.mp hN
    refine hD.conj_mem_of_img hJL ⟨l, hlN⟩ (fun l' hl' => L.mul_mem (L.mul_mem hlL hl')
      (L.inv_mem hlL)) fun q hq => ?_
    rw [hJ] at hq ⊢
    obtain ⟨v, hv, rfl⟩ := hq
    rw [← hw, ← map_inv, ← map_mul, ← map_mul]
    exact ⟨_, hblock v hv, rfl⟩
  have hNor : (J.subgroupOf (L ⊓ Subgroup.centralizer ({(b' : G)} : Set G))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hnorm g g.2 n hn⟩
  have hcard : 4 ≤ (Finset.univ.erase c).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ, Fintype.card_fin]
    norm_num
  exact ⟨hJA, CFSG.Assembly.IsSubnormal.step hJA hNor (CFSG.Assembly.IsSubnormal.refl _),
    ggQTwoDUnitSix_J_quasisimple hK (Finset.univ.erase c) hcard hθ hθr⟩

theorem ggQTwoDUnitSix_J_comp (hK : Nat.card K = 4) (hD : NsQuot.Datum p N f L Bs Z)
    (hψr : ψ.range = NsQuot.img N f L) (c : Fin 6) {J : Subgroup G} (hJL : J ≤ L)
    [Group.IsPerfect ↥J] (hJZ : ∀ j ∈ J, j ∈ Z → j = 1)
    (hJ : NsQuot.img N f J = (coordBlockSU K 2 1 (Finset.univ.erase c)).map ψ)
    (hψk : ψ.ker ≤ Subgroup.center (Su K 2 1 6))
    {θ : Su K 2 1 (Finset.univ.erase c).card →* G} (hθ : Function.Injective θ)
    (hθr : θ.range = J)
    (hθf : ∀ X, ∃ hN : θ X ∈ N, f ⟨θ X, hN⟩ = ψ (blockSUOn K 2 1 (Finset.univ.erase c) X))
    {b' : ↥N} (hb'L : ∀ l ∈ L, (b' : G) * l * (b' : G)⁻¹ ∈ L) {ω : Kˣ} (hω : orderOf ω = 3)
    (hb' : qTwoChartTwoThree_induces ψ (f b') (qtwoDB39_delDiag ω c)) {x : G}
    (hL : CFSG.Assembly.IsComponentOf L (Subgroup.centralizer ({x} : Set G))) :
    CFSG.Assembly.IsComponentOf J (Subgroup.centralizer ({(b' : G)} : Set G) ⊓
      Subgroup.centralizer ({x} : Set G)) := by
  have hJc := ggQTwoDUnitSix_J_comp_L hK hD hψr c hJL hJZ hJ hψk hθ hθr hθf hb'L hω hb'
  have h := isComponentOf_of_isSubnormal_of_isComponentOf hJc
    (LocalAnalysis.ComponentInitial.assembly_isSubnormal_inf hL.2.1
      (Subgroup.centralizer ({(b' : G)} : Set G)))
  rwa [inf_comm (Subgroup.centralizer ({x} : Set G))] at h

variable {B Bs' : Subgroup G} {x : G} {D J' : Subgroup G} {𝒦 : Finset (Subgroup G)}

theorem ggQTwoDUnitSix_signLift {βL : Additive ↥Bs ≃+ DVec 6}
    (hjoin : ∀ w ∈ dEven 6, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s))) {a c : Fin 6}
    (hac : a ≠ c) :
    ∃ α ∈ ggAutomizerJoin L Bs 𝒦,
      (∀ s : ↥Bs, βL (Additive.ofMul (α s)) = dSign 6 a c (βL (Additive.ofMul s))) ∧
      ∃ g ∈ L ⊔ ⨆ K ∈ 𝒦, K, g ∈ Subgroup.normalizer (Bs : Set G) ∧
        ∀ s : ↥Bs, ((α s : ↥Bs) : G) = g * (s : G) * g⁻¹ := by
  obtain ⟨α, hα, hαact⟩ := hjoin (dSign 6 a c) (dSign_mem_dEven hac)
  exact ⟨α, hα, hαact, exists_lift_of_mem_ggAutomizerJoin hα⟩

end CFSG.StandardType.QTwo

end
