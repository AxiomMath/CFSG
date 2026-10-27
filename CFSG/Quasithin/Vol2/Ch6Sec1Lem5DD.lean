module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DA
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DB
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DC
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5CentD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

abbrev cXU615 (T L H : Subgroup G) : Subgroup G :=
  (borelL T L ⊔ H) ⊓
    Subgroup.centralizer (conjClosure (quasithinOmegaOneCenter T) (borelL T L ⊔ H) : Set G)

omit [Finite G] in
theorem le_normalizer_cXU615 {T L H : Subgroup G} :
    borelL T L ⊔ H ≤ Subgroup.normalizer (cXU615 T L H : Set G) := fun _ hg =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer hg, le_normalizer_centralizer_ch6 (le_normalizer_conjClosure _ _) hg⟩

omit [Finite G] in
theorem cXU615_le_centralizer {T L H : Subgroup G} :
    cXU615 T L H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
  inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr (le_conjClosure _ _)))

namespace Cx615C

theorem false_of_closure_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n) {s : Set G}
    (hodd : ∀ y ∈ s, Odd (orderOf y)) (hsX : s ⊆ (borelL T L ⊔ H : Subgroup G))
    (hXs : ∀ g ∈ borelL T L ⊔ H, ∀ y ∈ s, g * y * g⁻¹ ∈ s)
    (hLs : ∀ y ∈ s, ∀ l ∈ L, l * y * l⁻¹ * y⁻¹ ∈ T) (hne : ∃ y ∈ s, y ≠ 1) : False := by
  have h := c.hyp
  set X := borelL T L ⊔ H with hXdef
  set Y := Subgroup.closure s with hYdef
  have hTH : T ≤ H := c.hH.1.1
  have hTX : T ≤ X := hTH.trans le_sup_right
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hconj : ∀ g : G, (∀ y ∈ s, g * y * g⁻¹ ∈ Y) → g ∈ Subgroup.normalizer (Y : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem_ch6
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hg x hx
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using Y.mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using Y.inv_mem ih
  have hXY : X ≤ Subgroup.normalizer (Y : Set G) := fun g hg =>
    hconj g fun y hy => Subgroup.subset_closure (hXs g hg y hy)
  have hTY : T ≤ Subgroup.normalizer (Y : Set G) := hTX.trans hXY
  have hLY : L ≤ Subgroup.normalizer (Y : Set G) := by
    intro l hl
    refine hconj l fun y hy => ?_
    have hmem : l * y * l⁻¹ ∈ Y ⊔ T := by
      have e : l * y * l⁻¹ = (l * y * l⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hLs y hy l hl))
        (Subgroup.mem_sup_left (Subgroup.subset_closure hy))
    have hodd' : Odd (orderOf (l * y * l⁻¹)) := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hodd y hy
    exact mem_of_odd_of_mem_sup_ch615 hT2 hTY hmem hodd'
  have hYX : Y ≤ X := (Subgroup.closure_le _).mpr hsX
  have hchar : CharTwo X := charTwo_of_inH' h.qtke h.sylow ⟨hTX, c.X_O2⟩
  have hOY : pCoreOf 2 Y ≠ ⊥ := by
    intro hOY
    obtain ⟨y, hy, hy1⟩ := hne
    apply hy1
    have hYO : Y ⊓ pCoreOf 2 X ≤ pCoreOf 2 Y := by
      refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
        ((pCoreOf_isPGroup 2 X).to_le inf_le_right)
      intro g hg
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, le_normalizer_pCoreOf 2 X (hYX hg)⟩
    rw [hOY] at hYO
    have hcomm : ⁅Y, pCoreOf 2 X⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (le_inf ?_ ?_) hYO)
      · exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((pCoreOf_le 2 X).trans hXY)
      · exact Subgroup.le_normalizer_iff_commutator_le_right.mp
          (hYX.trans (le_normalizer_pCoreOf 2 X))
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    have hYO2 : Y ≤ pCoreOf 2 X := (le_inf hYX hcomm).trans hchar
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 X ⟨y, hYO2 (Subgroup.subset_closure hy)⟩
    have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h2 : Nat.Coprime (orderOf y) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr (hodd y hy))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd h2 (orderOf_dvd_of_pow_eq_one hk'))
  have hNY : Subgroup.normalizer (Y : Set G) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 Y
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 Y : Set G)) :=
    ⟨pCoreOf 2 Y, hOY, pCoreOf_isPGroup 2 Y, rfl⟩
  have hLT : L ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) := (sup_le hLY hTY).trans hNY
  exact c.hH.2.1 (((le_sup_right : H ≤ X).trans (hXY.trans hNY)).trans
    (le_of_isUniqueM_of_le_twoLocal (h.isUniqueM h432) hLT hloc))

end Cx615C

namespace Cx615C

theorem eq_one_of_mem_permKer_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hCM : cXU615 T L H ≤ M) {F : Type} [Field F] [Finite F] [CharP F 2]
    {ψ : ↥(autOn L ⁅V, L⁆) ≃* SL(2, F)} {Y : ↥⁅V, L⁆ →* Multiplicative (Fin 2 → F)}
    (hcW : QCoord L ⁅V, L⁆ (T ⊓ L) F ψ Y) {g : G} (hgC : g ∈ cXU615 T L H)
    (hgK : g ∈ hcW.permKer615) (hodd : Odd (orderOf g)) : g = 1 := by
  classical
  by_contra hg1
  have h := c.hyp
  set Z := quasithinOmegaOneCenter T with hZdef
  set C := cXU615 T L H with hCdef
  set X := borelL T L ⊔ H with hXdef
  have hTH : T ≤ H := c.hH.1.1
  have hBX : borelL T L ≤ X := le_sup_left
  have hCX : C ≤ X := inf_le_left
  have hXC : X ≤ Subgroup.normalizer (C : Set G) := le_normalizer_cXU615
  have hCZ : C ≤ Subgroup.centralizer (Z : Set G) := cXU615_le_centralizer
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := hCM.trans h.normal
  have hCTL : C ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    refine le_trans (le_inf hCM ?_) c.CMZ
    exact hCZ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))
  have hWZ : ⁅V, L⁆ = ⁅Z, L⁆ := c.commutator_Z_eq_ch615.symm
  have hCW : C ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    rw [hWZ]
    exact le_normalizer_commutator_ch6 (le_normalizer_of_le_centralizer_ch615 hCZ) hCL
  have hCNL : C ≤ QCoord.normNL ⁅V, L⁆ L := le_inf hCW hCL
  have hCB : C ≤ Subgroup.normalizer (borelL T L : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hCL hy, Subgroup.le_normalizer (hCTL hy)⟩
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hsyl := c.toCx615.isSylowTwoOf_inf
  have hLW : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hcW.le_normalizer
  have hZT : Z ≤ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.2
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZT
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hTW : T ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    rw [hWZ]
    exact le_normalizer_commutator_ch6 (le_normalizer_of_le_centralizer_ch615 hTZ) hTL
  obtain ⟨z, hz, hzL⟩ : ∃ z ∈ Z ⊓ ⁅V, L⁆, z ∉ Subgroup.centralizer (L : Set G) := by
    by_contra hall
    exact c.ZL fun x hx => by
      by_contra hxL
      exact hall ⟨x, hx, hxL⟩
  have hzW : z ∈ ⁅V, L⁆ := hz.2
  have hWL : ¬ L ≤ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun hle => hzL
    (Subgroup.mem_centralizer_iff.mpr fun l hl =>
      (Subgroup.mem_centralizer_iff.mp (hle hl) z hzW).symm)
  have hCWT : (L ⊔ T) ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ T :=
    hS.sup_inf_centralizer_le (sup_le hLW hTW) hWL
  have hzT : z ∈ Subgroup.centralizer (T : Set G) := hZT hz.1
  have hz1 : Multiplicative.toAdd (Y ⟨z, hzW⟩) 1 = 0 := by
    refine (hcW.snd_eq_zero_iff inf_le_right ⟨z, hzW⟩).mpr fun s hs => ?_
    have hsz : s * z * s⁻¹ = z := by
      rw [Subgroup.mem_centralizer_iff.mp hzT s hs.1, mul_inv_cancel_right]
    show s * z * s⁻¹ * z⁻¹ ∈ _
    rw [hsz, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hz0 : Multiplicative.toAdd (Y ⟨z, hzW⟩) ≠ 0 := fun h0 => hzL ((hcW.ker _).mp
    (Multiplicative.toAdd.injective (by rw [h0, toAdd_one])))
  have hyz : ∀ y ∈ C, y * z * y⁻¹ = z := fun y hy => by
    rw [← Subgroup.mem_centralizer_iff.mp (hCZ hy) z hz.1, mul_inv_cancel_right]
  have hcomm : ∀ y ∈ C, ∀ δ ∈ borelL T L, y * δ * y⁻¹ * δ⁻¹ ∈ C ⊓ borelL T L := by
    intro y hy δ hδ
    refine ⟨?_, ?_⟩
    · have h1 : δ * y⁻¹ * δ⁻¹ ∈ C :=
        (Subgroup.mem_normalizer_iff.mp (hXC (hBX hδ)) _).mp (C.inv_mem hy)
      have e1 : y * δ * y⁻¹ * δ⁻¹ = y * (δ * y⁻¹ * δ⁻¹) := by group
      rw [e1]
      exact C.mul_mem hy h1
    · have h1 : y * δ * y⁻¹ ∈ borelL T L := (Subgroup.mem_normalizer_iff.mp (hCB hy) δ).mp hδ
      exact (borelL T L).mul_mem h1 ((borelL T L).inv_mem hδ)
  have hyD : ∀ y ∈ C, ∀ δ ∈ D, y * δ * y⁻¹ * δ⁻¹ * z = z * (y * δ * y⁻¹ * δ⁻¹) :=
    fun y hy δ hδ => (Subgroup.mem_centralizer_iff.mp (hCZ (hcomm y hy δ (hD.1 hδ)).1) z hz.1).symm
  have hWL2 : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
    intro hWL2
    apply h.module.2.2
    have h1 : ⁅⁅L, V⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L V]; exact hWL2
    have h3 : ⁅⁅L, L⁆, V⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 hWL2
    rw [h.toHyp5_0_1.commutator_eq] at h3
    rw [Subgroup.commutator_comm]
    exact h3
  have hLO : L ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ pCoreOf 2 L :=
    h.toHyp5_0_1.inf_centralizer_le hLW hWL2
  have hOLT : pCoreOf 2 L ≤ T := (F7.isSylowTwoOf_pCoreOf_le hsyl).trans inf_le_left
  have hg1' : orderOf g ≠ 1 := fun h1 => hg1 (orderOf_eq_one_iff.mp h1)
  obtain ⟨p, hp, hpg⟩ := Nat.exists_prime_and_dvd hg1'
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := fun h2 => by
    rw [h2] at hpg
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hpg)
  set x₁ := g ^ (orderOf g / p) with hx₁
  have hx₁p : orderOf x₁ = p := orderOf_pow_orderOf_div (orderOf_pos g).ne' hpg
  have hx₁C : x₁ ∈ C := C.pow_mem hgC _
  have hx₁K : x₁ ∈ hcW.permKer615 := hcW.permKer615.pow_mem hgK _
  have hkey : ∀ x ∈ C, x ^ p = 1 → x ∈ hcW.permKer615 := by
    by_cases hpF : p ∣ Nat.card F - 1
    · obtain ⟨d, hdD, hdp⟩ := hcW.exists_orderOf_eq_ch615 hCWT hsyl hD hpF
      have hdB : d ∈ borelL T L := hD.1 hdD
      have hN2 : IsPGroup 2 ↥(C ⊓ borelL T L) :=
        c.isPGroup_borelL_inf_ch615.to_le (le_inf inf_le_right (inf_le_left.trans hCZ))
      have hcyc : ∀ P : Sylow p ↥C, IsCyclic P := fun P => by
        by_contra hP
        obtain ⟨E, hEC, hE, hEc⟩ := exists_elemAbelian_sq_ch615 hp2 P hP
        exact not_elemAbelian_sq_ch615 h.qtke h.maxTwoLocal.1 hp2 hCM
          (inf_le_left.trans h.L_le) hdB hdp hCB (hBX.trans hXC) hN2 hEC hE hEc
      have hKn : (hcW.permKer615.subgroupOf C).Normal := ⟨fun a ha b => by
        rw [Subgroup.mem_subgroupOf] at ha ⊢
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact (Subgroup.mem_normalizer_iff.mp
          (hcW.normNL_le_normalizer_permKer615 (hCNL b.2)) _).mp ha⟩
      intro x hxC hxp
      have hmem := mem_of_isCyclic_sylow_ch615 hcyc hKn (x₁ := ⟨x₁, hx₁C⟩)
        (Subgroup.mem_subgroupOf.mpr hx₁K) (by rw [Subgroup.orderOf_mk]; exact hx₁p)
        (x := ⟨x, hxC⟩) (Subtype.ext (by simp [hxp]))
      exact Subgroup.mem_subgroupOf.mp hmem
    · intro x hxC hxp
      have hxNL := hCNL hxC
      refine hcW.mem_permKer615_iff.mpr ⟨hxNL, ?_⟩
      exact hcW.permHom_eq_one_ch615 hCWT hsyl hD hzW hz1 hz0 ⟨x, hxNL⟩ (hyz x hxC)
        (hyD x hxC) hp hp2 hpF (Subtype.ext (by simp [hxp]))
  refine false_of_closure_ch615 h432 c (s := {x | x ∈ C ∧ x ^ p = 1}) ?_ ?_ ?_ ?_
    ⟨x₁, ⟨hx₁C, ?_⟩, ?_⟩
  · rintro y ⟨-, hy⟩
    exact Odd.of_dvd_nat (hp.odd_of_ne_two hp2) (orderOf_dvd_of_pow_eq_one hy)
  · rintro y ⟨hy, -⟩
    exact hCX hy
  · rintro g' hg' y ⟨hyC, hyp⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hXC hg') y).mp hyC, ?_⟩
    rw [conj_pow, hyp, mul_one, mul_inv_cancel]
  · rintro y ⟨hyC, hyp⟩ l hl
    have hyK := hkey y hyC hyp
    have hc1 : l * y * l⁻¹ * y⁻¹ ∈ L := by
      have h1 : y * l⁻¹ * y⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hCL hyC) _).mp (L.inv_mem hl)
      have e1 : l * y * l⁻¹ * y⁻¹ = l * (y * l⁻¹ * y⁻¹) := by group
      rw [e1]
      exact L.mul_mem hl h1
    have hlNL : l ∈ QCoord.normNL ⁅V, L⁆ L := ⟨hLW hl, Subgroup.le_normalizer hl⟩
    have hc2 : l * y * l⁻¹ * y⁻¹ ∈ hcW.permKer615 :=
      hcW.permKer615.mul_mem ((Subgroup.mem_normalizer_iff.mp
        (hcW.normNL_le_normalizer_permKer615 hlNL) y).mp hyK) (hcW.permKer615.inv_mem hyK)
    exact hOLT (hLO ⟨hc1, hcW.inf_permKer615_le ⟨hc1, hc2⟩⟩)
  · rw [← hx₁p]
    exact pow_orderOf_eq_one x₁
  · intro h1
    rw [h1, orderOf_one] at hx₁p
    exact hp.one_lt.ne hx₁p

end Cx615C

namespace Cx615C

theorem le_normalizer_pCoreOf_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hCM : cXU615 T L H ≤ M) :
    cXU615 T L H ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) := by
  classical
  have h := c.hyp
  set Z := quasithinOmegaOneCenter T with hZdef
  set C := cXU615 T L H with hCdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  have hsyl := c.toCx615.isSylowTwoOf_inf
  obtain ⟨F, _, _, _, -, ψ, Y, hcW⟩ := c.nat.commutator.exists_qcoord hsyl
  set K := hcW.permKer615 with hKdef
  have hTH : T ≤ H := c.hH.1.1
  have hTX : T ≤ borelL T L ⊔ H := hTH.trans le_sup_right
  have hXC : borelL T L ⊔ H ≤ Subgroup.normalizer (C : Set G) := le_normalizer_cXU615
  have hTC : T ≤ Subgroup.normalizer (C : Set G) := hTX.trans hXC
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hCZ : C ≤ Subgroup.centralizer (Z : Set G) := cXU615_le_centralizer
  have hCL : C ≤ Subgroup.normalizer (L : Set G) := hCM.trans h.normal
  have hWZ : ⁅V, L⁆ = ⁅Z, L⁆ := c.commutator_Z_eq_ch615.symm
  have hZT : Z ≤ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr fun x hx => hx.1.2
  have hTZ : T ≤ Subgroup.centralizer (Z : Set G) := Subgroup.le_centralizer_iff.mp hZT
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.T_le.trans h.normal
  have hLW : L ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hcW.le_normalizer
  have hTW : T ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    rw [hWZ]
    exact le_normalizer_commutator_ch6 (le_normalizer_of_le_centralizer_ch615 hTZ) hTL
  have hCW : C ≤ Subgroup.normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    rw [hWZ]
    exact le_normalizer_commutator_ch6 (le_normalizer_of_le_centralizer_ch615 hCZ) hCL
  have hCTNL : C ⊔ T ≤ QCoord.normNL ⁅V, L⁆ L := sup_le (le_inf hCW hCL) (le_inf hTW hTL)
  have hLTNL : L ⊔ T ≤ QCoord.normNL ⁅V, L⁆ L :=
    sup_le (le_inf hLW Subgroup.le_normalizer) (le_inf hTW hTL)
  set K₂ := (C ⊔ T) ⊓ K with hK₂
  have hK₂2 : IsPGroup 2 ↥K₂ := by
    rintro ⟨x, hxCT, hxK⟩
    obtain ⟨k, m, hm, hxm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
    have hx' : (x ^ 2 ^ k) ^ m = 1 := by rw [← pow_mul, ← hxm, pow_orderOf_eq_one]
    have hodd : Odd (orderOf (x ^ 2 ^ k)) := Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hx')
    have hxC : x ^ 2 ^ k ∈ C :=
      mem_of_odd_of_mem_sup_ch615 hT2 hTC ((C ⊔ T).pow_mem hxCT _) hodd
    have h1 := c.eq_one_of_mem_permKer_ch615 h432 hCM hcW hxC (K.pow_mem hxK _) hodd
    exact ⟨k, Subtype.ext (by simpa using h1)⟩
  have hK₂n : C ⊔ T ≤ Subgroup.normalizer (K₂ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hg, hcW.normNL_le_normalizer_permKer615 (hCTNL hg)⟩
  have hK₂T : K₂ ≤ T :=
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hK₂n hK₂2).trans
      (F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf le_sup_right))
  obtain ⟨D, hD⟩ := c.exists_hall_ch615
  have hS := h.toHyp5_0_1.setting516 hD h.module
  have hWL2 : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
    intro hWL2
    apply h.module.2.2
    have h1 : ⁅⁅L, V⁆, L⁆ = ⊥ := by rw [Subgroup.commutator_comm L V]; exact hWL2
    have h3 : ⁅⁅L, L⁆, V⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 hWL2
    rw [h.toHyp5_0_1.commutator_eq] at h3
    rw [Subgroup.commutator_comm]
    exact h3
  have hLO : L ⊓ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) ≤ pCoreOf 2 L :=
    h.toHyp5_0_1.inf_centralizer_le hLW hWL2
  have hPW : (L ⊔ T) ⊓ K ≤ Q := by
    refine hS.le_pCoreOf_of_inf_le inf_le_left (fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, hcW.normNL_le_normalizer_permKer615 (hLTNL hg)⟩) ?_
    rintro x ⟨hxL, -, hxK⟩
    exact hLO ⟨hxL, hcW.inf_permKer615_le ⟨hxL, hxK⟩⟩
  have hQT : Q ≤ T := F7.isSylowTwoOf_pCoreOf_le (h.toHyp5_0_1.isSylowTwoOf le_sup_right)
  have hWV : ⁅V, L⁆ ≤ V :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (le_sup_left.trans c.V_facts.2.1)
  have hQW : Q ≤ Subgroup.centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := by
    rw [hQdef, ← h.centralizer_eq]
    exact inf_le_right.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hWV))
  have hQK₂ : Q ≤ K₂ := fun x hx => ⟨Subgroup.mem_sup_right (hQT hx),
    hcW.mem_permKer615_iff.mpr ⟨hLTNL (Subgroup.mem_sup_right (hQT hx)),
      hcW.permHom_eq_one _ (hQW hx)⟩⟩
  have heq : K₂ = Q := le_antisymm (fun x hx => hPW ⟨Subgroup.mem_sup_right (hK₂T hx), hx.2⟩)
    hQK₂
  intro g hg
  rw [← heq]
  exact hK₂n (Subgroup.mem_sup_left hg)

theorem le_normalizer_baum_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hCM : cXU615 T L H ≤ M) :
    cXU615 T L H ≤ Subgroup.normalizer (baum ((T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T)) : Set G) := by
  intro g hg
  apply normalizer_le_normalizer_baum
  have hCZ : cXU615 T L H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
    cXU615_le_centralizer
  have h1 : g ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    refine c.CMZ ⟨hCM hg, ?_⟩
    exact (hCZ.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left))) hg
  have h2 := c.le_normalizer_pCoreOf_ch615 h432 hCM hg
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h1 h2 ⊢
  rw [Subgroup.map_sup, h1, h2]

end Cx615C

end CFSG.Quasithin.H13
