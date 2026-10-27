module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829L3M22
public import CFSG.Quasithin.Background.B682Ambient
public import CFSG.Quasithin.Vol2.Ch10SecEL0
public import CFSG.Quasithin.Background.RonanD33

public section

namespace CFSG.Quasithin.H13

section LM1

theorem eq_top_of_not_le_frattini_of_isCyclic {X : Type} [Group X] [Finite X] {p : ℕ}
    [hp : Fact p.Prime] [hc : IsCyclic X] (hX : IsPGroup p X) (S : Subgroup X)
    (hS : ¬ S ≤ frattini X) : S = ⊤ := by
  by_contra hne
  apply hS
  have hK : S ⊔ frattini X ≠ ⊤ := fun h => hne (frattini_nongenerating h)
  obtain ⟨C, hC, hSC⟩ := (eq_top_or_exists_le_coatom (S ⊔ frattini X)).resolve_left hK
  have hindex : ∀ D : Subgroup X, IsCoatom D → D = C := by
    intro D hD
    apply (IsCyclic.subgroup_eq_iff_index_eq).mpr
    rw [(IsPGroup.isCoatom_iff_index_eq_prime hX).mp hD,
      (IsPGroup.isCoatom_iff_index_eq_prime hX).mp hC]
  have hSD : ∀ D : Subgroup X, IsCoatom D → S ≤ D := by
    intro D hD
    rw [hindex D hD]
    exact le_sup_left.trans hSC
  unfold frattini Order.radical
  exact le_iInf₂ fun D hD => hSD D hD

variable {X : Type} [Group X] [Finite X]

theorem oTwoUpper_subgroup_map_le (A : Subgroup X) :
    (oTwoUpper (⊤ : Subgroup A)).map A.subtype ≤ oTwoUpper A := by
  unfold oTwoUpper
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  apply Subgroup.subset_closure
  exact ⟨x.2, by
    show Odd (orderOf (x : X))
    rw [Subgroup.orderOf_coe]
    exact hx.2⟩

theorem map_oTwoUpper_top_eq {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (ψ : A →* B) (hψ : Function.Surjective ψ) :
    (oTwoUpper (⊤ : Subgroup A)).map ψ = oTwoUpper (⊤ : Subgroup B) := by
  rw [← CFSG.Quasithin.Vol2.Ch10.SecE.twoResidual_eq_oTwoUpper,
    ← CFSG.Quasithin.Vol2.Ch10.SecE.twoResidual_eq_oTwoUpper, B6.twoResidual_map_top hψ]

theorem exists_lift_rotation {A : Type} [Group A] [Finite A] {m : ℕ} (hm : m.Prime)
    (hm2 : m ≠ 2) (ψ : A →* DihedralGroup m) (hψ : Function.Surjective ψ) :
    ∃ y ∈ oTwoUpper (⊤ : Subgroup A), ψ y = DihedralGroup.r (1 : ZMod m) := by
  haveI : NeZero m := ⟨hm.ne_zero⟩
  have hodd : Odd m := hm.odd_of_ne_two hm2
  have h1 : DihedralGroup.r (1 : ZMod m) ∈ oTwoUpper (⊤ : Subgroup (DihedralGroup m)) := by
    apply Subgroup.subset_closure
    refine ⟨Subgroup.mem_top _, ?_⟩
    rw [DihedralGroup.orderOf_r_one]
    exact hodd
  rw [← map_oTwoUpper_top_eq ψ hψ] at h1
  exact h1

theorem prime_eq_of_dihedral_core {p m : ℕ} [hp : Fact p.Prime] {Ix Mx : Subgroup X}
    (hm : m.Prime) (hm2 : m ≠ 2) (ψ : Ix →* DihedralGroup m) (hψs : Function.Surjective ψ)
    (hψJ : ∀ y : Ix, (y : X) ∈ kerIn Mx ⊤ → ψ y = 1)
    (hQJ : CFSG.Open.pCore 2 X ≤ kerIn Mx ⊤)
    (hO : oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) =
      CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X)) :
    m = p := by
  haveI : (CFSG.Open.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set Q := CFSG.Open.pCore 2 X with hQ
  set φ := QuotientGroup.mk' Q with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  have hφO : (oTwoUpper (⊤ : Subgroup X)).map φ = CFSG.Open.pCore p (X ⧸ Q) := by
    rw [map_oTwoUpper_top_eq φ hφs, hO]
  obtain ⟨y, hy, hyr⟩ := exists_lift_rotation hm hm2 ψ hψs
  have hyX : (y : X) ∈ oTwoUpper (⊤ : Subgroup X) :=
    oTwoUpper_mono le_top (oTwoUpper_subgroup_map_le Ix (Subgroup.mem_map_of_mem Ix.subtype hy))
  have hφy : φ (y : X) ∈ CFSG.Open.pCore p (X ⧸ Q) := by
    rw [← hφO]
    exact Subgroup.mem_map_of_mem φ hyX
  obtain ⟨a, ha⟩ := CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ Q) p ⟨_, hφy⟩
  have ha' : φ ((y : X) ^ p ^ a) = 1 := by
    rw [map_pow]
    exact congrArg Subtype.val ha
  have hpowQ : (y : X) ^ p ^ a ∈ Q := (QuotientGroup.eq_one_iff _).mp ha'
  have hyJ : ((y ^ p ^ a : Ix) : X) ∈ kerIn Mx ⊤ := hQJ hpowQ |> fun h => by
    simpa [Subgroup.coe_pow] using h
  have hrpow : DihedralGroup.r (1 : ZMod m) ^ p ^ a = 1 := by
    rw [← hyr, ← map_pow, hψJ _ hyJ]
  rw [← orderOf_dvd_iff_pow_eq_one, DihedralGroup.orderOf_r_one] at hrpow
  have hmp : m ∣ p := hm.dvd_of_dvd_pow hrpow
  exact (Nat.prime_dvd_prime_iff_eq hm hp.out).mp hmp


theorem oTwoUpper_le_of_isCyclic_core {p m : ℕ} [hp : Fact p.Prime] {Ix Mx : Subgroup X}
    (hm : m.Prime) (hm2 : m ≠ 2) (ψ : Ix →* DihedralGroup m) (hψs : Function.Surjective ψ)
    (hψJ : ∀ y : Ix, (y : X) ∈ kerIn Mx ⊤ → ψ y = 1)
    (hQJ : CFSG.Open.pCore 2 X ≤ kerIn Mx ⊤)
    (hO : oTwoUpper (⊤ : Subgroup (X ⧸ CFSG.Open.pCore 2 X)) =
      CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X))
    (hJbar : (kerIn Mx ⊤).map (QuotientGroup.mk' (CFSG.Open.pCore 2 X)) =
      (frattini ↥(CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X))).map
        (CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X)).subtype)
    (hcyc : IsCyclic ↥(CFSG.Open.pCore p (X ⧸ CFSG.Open.pCore 2 X))) :
    oTwoUpper (⊤ : Subgroup X) ≤ Ix ⊔ kerIn Mx ⊤ := by
  haveI : (CFSG.Open.pCore 2 X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  set Q := CFSG.Open.pCore 2 X with hQ
  set φ := QuotientGroup.mk' Q with hφ
  have hφs : Function.Surjective φ := QuotientGroup.mk'_surjective Q
  set P := CFSG.Open.pCore p (X ⧸ Q) with hP
  have hPp : IsPGroup p ↥P := CFSG.LieType.BorelTits.pCore_isPGroup (G := X ⧸ Q) p
  haveI : IsCyclic ↥P := hcyc
  have hφO : (oTwoUpper (⊤ : Subgroup X)).map φ = P := by
    rw [map_oTwoUpper_top_eq φ hφs, hO]
  have hSP : (oTwoUpper Ix).map φ ≤ P := by
    rw [← hφO]
    exact Subgroup.map_mono (oTwoUpper_mono le_top)
  set S' : Subgroup ↥P := ((oTwoUpper Ix).map φ).subgroupOf P with hS'
  have hJS : (kerIn Mx ⊤).map φ = (frattini ↥P).map P.subtype := hJbar
  have hnot : ¬ S' ≤ frattini ↥P := by
    intro hle
    have hOJ : ∀ y ∈ oTwoUpper Ix, y ∈ kerIn Mx ⊤ := by
      intro y hy
      have hPy : φ y ∈ P := hSP (Subgroup.mem_map_of_mem φ hy)
      have hmem : (⟨φ y, hPy⟩ : ↥P) ∈ S' :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem φ hy)
      have hJy : φ y ∈ (kerIn Mx ⊤).map φ := by
        rw [hJS]
        exact Subgroup.mem_map_of_mem P.subtype (hle hmem)
      obtain ⟨j, hj, hjy⟩ := Subgroup.mem_map.mp hJy
      have key : φ (j⁻¹ * y) = 1 := by
        rw [map_mul, map_inv, hjy, inv_mul_cancel]
      have hq : j⁻¹ * y ∈ Q := by
        have h2 : j⁻¹ * y ∈ (QuotientGroup.mk' Q).ker := MonoidHom.mem_ker.mpr key
        rwa [QuotientGroup.ker_mk'] at h2
      have hy' : y = j * (j⁻¹ * y) := by group
      rw [hy']
      exact (kerIn Mx ⊤).mul_mem hj (hQJ hq)
    obtain ⟨y, hy, hyr⟩ := exists_lift_rotation hm hm2 ψ hψs
    have hyI : ((y : Ix) : X) ∈ oTwoUpper Ix :=
      oTwoUpper_subgroup_map_le Ix (Subgroup.mem_map_of_mem Ix.subtype hy)
    have h1 : ψ y = 1 := hψJ y (hOJ _ hyI)
    rw [hyr] at h1
    have hord := DihedralGroup.orderOf_r_one (n := m)
    rw [h1, orderOf_one] at hord
    have := hm.one_lt
    omega
  have hS'top : S' = ⊤ := eq_top_of_not_le_frattini_of_isCyclic hPp S' hnot
  intro z hz
  have hzP : φ z ∈ P := by
    rw [← hφO]
    exact Subgroup.mem_map_of_mem φ hz
  have hmem : (⟨φ z, hzP⟩ : ↥P) ∈ S' := by
    rw [hS'top]
    exact Subgroup.mem_top _
  obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hmem)
  have key : φ (y⁻¹ * z) = 1 := by
    rw [map_mul, map_inv, hyz]
    exact inv_mul_cancel _
  have hq : y⁻¹ * z ∈ Q := by
    have h2 : y⁻¹ * z ∈ (QuotientGroup.mk' Q).ker := MonoidHom.mem_ker.mpr key
    rwa [QuotientGroup.ker_mk'] at h2
  have hz' : z = y * (y⁻¹ * z) := by group
  rw [hz']
  exact Subgroup.mul_mem_sup (oTwoUpper_le Ix hy) (hQJ hq)

end LM1

section LM1Wrap

@[expose] def StmtD3L3M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
          ∃ m : ℕ, (m = 3 ∨ m = 5) ∧
            Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
              DihedralGroup m)

@[expose] def StmtFelemL3M22 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G), Hyp7_0_2 G T L I → Hyp7_3_1 T L I →
    Hyp8_2_1 T L I → ∀ _ : IsMulCommutative ↥(fsuV T I), Case8_2 T L I →
      ∀ (H : Subgroup G) (h : G) (k : ℕ), IsHStar T (fsuM T L) H → h ∈ H →
        Concl822 T L I H h k → (Row711L3Nine T L I 1 ∨ Row711M22Code T L I) →
          ∀ p : ℕ, (p = 3 ∨ p = 5) → ∃ f ∈ ch82LU L (ch82U (fsuV T I) h), f ^ p = 1 ∧
            f ∉ Subgroup.centralizer (ch82U (fsuV T I) h : Set G)

theorem l3M22Solv_of (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h825 : Stmt8_2_5)
    (h828 : Stmt8_2_8) (hD3 : StmtD3L3M22) (hF : StmtFelemL3M22) : L3M22Solv := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' hsolv
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hC8 := h828 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨-, hL0, hTL, -, -, -, -, -, -, -, -, -, -⟩ := setup_828 hmod h711n hyp hrow hC hC5
  have hTM : T ≤ fsuM T L := by
    show T ≤ Subgroup.normalizer (fsuL0 T L : Set G)
    rw [hL0]
    exact hTL
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hTsyl : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hnN : ¬ H ≤ Subgroup.normalizer (T : Set G) := fun hle =>
    hC.1 (hVT.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hH.1.1 hle hT2))
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hUM : IsUniqueMaxOver H T (H ⊓ fsuM T L) := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hTM)
    rwa [hP] at this
  have hMP : MinParabolic H T (H ⊓ fsuM T L) := ⟨hTsyl, hnN, hUM⟩
  obtain ⟨p, hpp, hp2, hO2p2, hJbar, -, -⟩ := hMP.subgroupOf.solvable_structure hsolv
  haveI : Fact p.Prime := ⟨hpp⟩
  have hquot : ∀ y : ↥H ⧸ CFSG.Open.pCore 2 ↥H, ∃ j : ℕ,
      y ^ 2 ^ j ∈ CFSG.Open.pCore p (↥H ⧸ CFSG.Open.pCore 2 ↥H) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) y
    obtain ⟨j, hj⟩ := (B6.upperTwo_eq_top_iff (O2p ↥H p)).mp hO2p2 x
    exact ⟨j, by rw [← map_pow]; exact Subgroup.mem_comap.mp hj⟩
  have hOt : twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)) =
      CFSG.Open.pCore p (↥H ⧸ CFSG.Open.pCore 2 ↥H) :=
    E2.twoResidual_eq_pCore hpp hp2 hquot
  have hO : oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)) =
      CFSG.Open.pCore p (↥H ⧸ CFSG.Open.pCore 2 ↥H) := by
    rw [← CFSG.Quasithin.Vol2.Ch10.SecE.twoResidual_eq_oTwoUpper]
    exact hOt
  have hHIT : H = ch82I (fsuV T I) h ⊔ T := H_eq_ch82I_sup_T_829 hmod hyp hH hC
  have hIH : ch82I (fsuV T I) h ≤ H := by
    rw [hHIT]
    exact le_sup_left
  obtain ⟨m, hm3, ⟨eD⟩⟩ := hD3 G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow'
  let e' : ↥((ch82I (fsuV T I) h).subgroupOf H) ≃* ↥(ch82I (fsuV T I) h) :=
    Subgroup.subgroupOfEquivOfLe hIH
  let πI : ↥(ch82I (fsuV T I) h) →* E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h)
      (ch82I (fsuV T I) h) := QuotientGroup.mk' _
  let ψ : ↥((ch82I (fsuV T I) h).subgroupOf H) →* DihedralGroup m :=
    eD.toMonoidHom.comp (πI.comp e'.toMonoidHom)
  have hψs : Function.Surjective ψ :=
    eD.surjective.comp ((QuotientGroup.mk'_surjective _).comp e'.surjective)
  have hm_prime : m.Prime := by
    rcases hm3 with rfl | rfl <;> norm_num
  have hm2 : m ≠ 2 := by
    rcases hm3 with rfl | rfl <;> norm_num
  have hJI : ∀ g : G, g ∈ kerIn (H ⊓ fsuM T L) H → g ∈ ch82I (fsuV T I) h →
      g ∈ kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) := by
    intro g hg hgI
    rw [mem_kerIn]
    intro b hb
    exact ⟨((mem_kerIn.mp hg) b (hIH hb)).2,
      (ch82I (fsuV T I) h).mul_mem ((ch82I (fsuV T I) h).mul_mem hb hgI)
        ((ch82I (fsuV T I) h).inv_mem hb)⟩
  have hψJ : ∀ y : ↥((ch82I (fsuV T I) h).subgroupOf H),
      ((y : ↥H)) ∈ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤ → ψ y = 1 := by
    intro y hy
    rw [B6.kerIn_subgroupOf_top, Subgroup.mem_subgroupOf] at hy
    have hk : e' y ∈ (kerIn (fsuM T L ⊓ ch82I (fsuV T I) h)
        (ch82I (fsuV T I) h)).subgroupOf (ch82I (fsuV T I) h) :=
      Subgroup.mem_subgroupOf.mpr (hJI _ hy (Subgroup.mem_subgroupOf.mp y.2))
    have hpi : πI (e' y) = 1 := (QuotientGroup.eq_one_iff (e' y)).mpr hk
    show eD (πI (e' y)) = 1
    rw [hpi, map_one]
  have hQT : CFSG.Open.pCore 2 ↥H ≤ T.subgroupOf H := by
    intro x hx
    have hle : CFSG.Open.pCoreOf 2 H ≤ T :=
      CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow hH.1.1 hT2 hTsyl.2.2
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem H.subtype hx))
  have hTM' : T.subgroupOf H ≤ (H ⊓ fsuM T L).subgroupOf H := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨x.2, hTM (Subgroup.mem_subgroupOf.mp hx)⟩)
  have hnormQ : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQJ : CFSG.Open.pCore 2 ↥H ≤ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤ := by
    intro x hx
    rw [mem_kerIn]
    intro b _
    exact hTM' (hQT (hnormQ.conj_mem x hx b))
  have hmp : m = p := prime_eq_of_dihedral_core hm_prime hm2 ψ hψs hψJ hQJ hO
  have hpm : p = 3 ∨ p = 5 := hmp ▸ hm3
  have hr : CFSG.Open.pRank p H ≤ 1 :=
    (pRank_le_one_82 hmod hp2 hyp hH hC hC5 hC8
      (hF G T L I hyp h731 h821 hc hrow H h k hH hh hC hrow' p hpm)).2
  have hpH : p ∣ Nat.card ↥H := by
    obtain ⟨y, hy⟩ := hψs (DihedralGroup.r (1 : ZMod m))
    have hr1 : orderOf (ψ y) = m := by
      rw [hy]
      exact DihedralGroup.orderOf_r_one
    have hdvd : orderOf (ψ y) ∣ Nat.card ↥H :=
      (orderOf_map_dvd ψ y).trans
        ((orderOf_dvd_natCard y).trans (Subgroup.card_subgroup_dvd_card _))
    rw [hr1] at hdvd
    rw [← hmp]
    exact hdvd
  have hcycH : IsCyclic ↥(twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H))) :=
    hMP.isCyclic_twoResidual_ambient hsolv hpp hp2 hpH hr
  rw [hOt] at hcycH
  have hsub : oTwoUpper (⊤ : Subgroup ↥H) ≤
      (ch82I (fsuV T I) h).subgroupOf H ⊔ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤ :=
    oTwoUpper_le_of_isCyclic_core hm_prime hm2 ψ hψs hψJ hQJ hO hJbar hcycH
  have hmapO : oTwoUpper H ≤ (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := by
    unfold oTwoUpper
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxo⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
    show Odd (orderOf (⟨x, hxH⟩ : ↥H))
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hIsub : ((ch82I (fsuV T I) h).subgroupOf H).map H.subtype = ch82I (fsuV T I) h :=
    Subgroup.map_subgroupOf_eq_of_le hIH
  have hJsub : (kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤).map H.subtype =
      kerIn (H ⊓ fsuM T L) H := by
    rw [B6.kerIn_subgroupOf_top, Subgroup.map_subgroupOf_eq_of_le (kerIn_le.trans inf_le_left)]
  calc oTwoUpper H ≤ (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := hmapO
    _ ≤ (((ch82I (fsuV T I) h).subgroupOf H) ⊔ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤).map
          H.subtype := Subgroup.map_mono hsub
    _ = ch82I (fsuV T I) h ⊔ kerIn (H ⊓ fsuM T L) H := by
          rw [Subgroup.map_sup, hIsub, hJsub]

end LM1Wrap

end CFSG.Quasithin.H13
