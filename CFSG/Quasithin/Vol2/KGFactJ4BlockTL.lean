module

public import CFSG.Milestones.ASVolI.C31.J4NP.Plane
public import CFSG.Quasithin.Vol2.KGFactJ4BlockC
public import CFSG.Quasithin.Vol2.KGFactJ4L5NSD
public import CFSG.Quasithin.Vol2.KGFactJ4L5NSDB

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace L52

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4

theorem le_conj_M4_of_twoLocal
    (hTL : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) {X : Subgroup J} (P : Subgroup J)
    (hP : IsPGroup 2 ↥P) (hP1 : P ≠ ⊥) (hXP : X ≤ Subgroup.normalizer (P : Set J))
    (h31 : 31 ∣ Nat.card X) :
    ∃ g : J, X ≤ CFSG.Quasithin.KGJ4.M4.map (MulAut.conj g).toMonoidHom := by
  have hF : J4Facts := j4Facts
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  have hcz : Nat.card ↥(Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)) =
      21799895040 := CFSG.Sporadic.J4.QT2.card_centralizer_z0 hF
  obtain ⟨g, hg⟩ := hTL P hP hP1
  rcases hg with h | h | h | h
  · exfalso
    have := h31.trans (Subgroup.card_dvd_of_le (hXP.trans h))
    rw [card_map_conj, card_Hj hF] at this
    norm_num at this
  · exfalso
    have := h31.trans (Subgroup.card_dvd_of_le (hXP.trans h))
    rw [card_map_conj, hcz] at this
    norm_num at this
  · exfalso
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 31 h31
    obtain ⟨n, hn, hny⟩ := (hXP.trans h) y.2
    have hord : orderOf n = 31 := by
      have h1 : orderOf ((y : ↥X) : J) = 31 := by rw [Subgroup.orderOf_coe]; exact hy
      rwa [← hny, MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq] at h1
    have hVC := le_centralizer_of_card_lt hord hn (by rw [J4L4.card_V0 j4Facts.mat]; norm_num)
    have hz0 : CFSG.Quasithin.J4Loc.z0 ∈ CFSG.Quasithin.J4Loc.V0 :=
      Subgroup.subset_closure (by simp [CFSG.Quasithin.J4Loc.z0])
    have hnC : n ∈ Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J) := by
      have := hVC hz0
      rw [Subgroup.mem_centralizer_singleton_iff] at this ⊢
      exact this.symm
    have := hord ▸ Subgroup.orderOf_dvd_natCard _ hnC
    rw [hcz] at this
    norm_num at this
  · exact ⟨g, hXP.trans h⟩

end L52

end CFSG.Quasithin.H13.Ch4.G443J4

namespace CFSG.Quasithin.H13.Ch4.J4Blk

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

attribute [local instance] finite_J

theorem normalizer_M4_tl :
    Subgroup.normalizer (CFSG.Quasithin.KGJ4.M4 : Set J) = CFSG.Quasithin.KGJ4.M4 := by
  refine le_antisymm ?_ Subgroup.le_normalizer
  intro n hn
  have h1 := normalizer_le_normalizer_pCoreOf 2 CFSG.Quasithin.KGJ4.M4 hn
  rw [pCoreOf_M4 j4Facts.mat chkF_true CFSG.Quasithin.J4M4Card.card_M4,
    CFSG.ASVolI.burnsideJ4NP_normalizer_F4] at h1
  exact h1

theorem centralizer_F4_tl :
    Subgroup.centralizer (F4 j4Facts.mat chkF_true : Set J) = F4 j4Facts.mat chkF_true :=
  CFSG.ASVolI.burnsideJ4NP_centralizer_F4

theorem blockConcl_M4_tl :
    BlockConcl CFSG.Quasithin.KGJ4.M4 := by
  have hO := pCoreOf_M4 j4Facts.mat chkF_true CFSG.Quasithin.J4M4Card.card_M4
  obtain ⟨x, hxM, hx3, h4⟩ := exists_orderOf_three_M4
  obtain ⟨h1, h2, h3, h5, h6⟩ := x_facts (isPGroup_F4 j4Facts.mat chkF_true) hx3 h4
  refine ⟨normalizer_M4_tl, ?_, ?_, x, hxM, hx3, ?_⟩
  · rw [hO]
    exact centralizer_F4_tl
  · rw [hO]
    exact m4_min j4Facts.mat chkF_true
  · rw [hO]
    exact ⟨h1, h2, h3, h5, h6⟩

theorem exists_hom_map_eq_tl
    (hTL : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) {K : Type} [Group K] (hK : IsSporadic .J4 K)
    (B : Subgroup K)
    (hE : IsExt ↥B (fun N _ => IsE2 11 N) (fun Y _ => IsSporadic .M24 Y) ∨
      IsExt ↥B (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y)) :
    ∃ f : K →* J, Function.Bijective f ∧
      (B.map f = Hj ∨ B.map f = CFSG.Quasithin.KGJ4.M4) := by
  obtain ⟨e⟩ := hK
  obtain ⟨φ, hφ⟩ : ∃ φ : K →* J, Function.Bijective φ :=
    ⟨(e.trans (seedEquiv j4Facts.mat) : K →* J), (e.trans (seedEquiv j4Facts.mat)).bijective⟩
  have hcB : Nat.card ↥(B.map φ) = Nat.card B := Subgroup.card_map_of_injective hφ.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hE with ⟨N, hN, hNE, hNQ⟩ | ⟨N, hN, hNE, hNQ⟩
  ·
    have hcN : Nat.card N = 2 ^ 11 := by
      obtain ⟨e'⟩ := hNE
      rw [Nat.card_congr e'.toEquiv]
      simp
    have hcQ : Nat.card (↥B ⧸ N) = 244823040 := by
      obtain ⟨e'⟩ := hNQ
      rw [Nat.card_congr e'.toEquiv]
      exact CFSG.Sporadic.Mathieu.card_M24
    have hcB' : Nat.card B = 501397585920 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hcQ, hcN]
      norm_num
    have hcN₁ : Nat.card ↥((N.map B.subtype).map φ) = 2 ^ 11 := by
      rw [Subgroup.card_map_of_injective hφ.1,
        Subgroup.card_map_of_injective B.subtype_injective, hcN]
    have hne : (N.map B.subtype).map φ ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcN₁
      norm_num at hcN₁
    have hNB : B.map φ ≤ Subgroup.normalizer (((N.map B.subtype).map φ : Subgroup J) : Set J) := by
      rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨_, ⟨m, hm, rfl⟩, rfl⟩ := hn
      refine ⟨_, ⟨⟨b, hb⟩ * m * ⟨b, hb⟩⁻¹, hN.conj_mem m hm ⟨b, hb⟩, rfl⟩, ?_⟩
      simp
    obtain ⟨g, hg⟩ := exists_conj_eq_Hj (hcB.trans hcB') (IsPGroup.of_card hcN₁) hne hNB
    refine ⟨(MulAut.conj g).toMonoidHom.comp φ, (MulAut.conj g).bijective.comp hφ, Or.inl ?_⟩
    rw [← Subgroup.map_map, hg]
  ·
    have hcN : Nat.card N = 2 ^ 10 := by
      obtain ⟨e'⟩ := hNE
      rw [Nat.card_congr e'.toEquiv]
      simp
    have hcB' : Nat.card B = 10239344640 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, F420.card_of_l52 hNQ, hcN]
      norm_num
    have hcN₁ : Nat.card ↥((N.map B.subtype).map φ) = 2 ^ 10 := by
      rw [Subgroup.card_map_of_injective hφ.1,
        Subgroup.card_map_of_injective B.subtype_injective, hcN]
    have hne : (N.map B.subtype).map φ ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcN₁
      norm_num at hcN₁
    have hNB : B.map φ ≤ Subgroup.normalizer (((N.map B.subtype).map φ : Subgroup J) : Set J) := by
      rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.mem_normalizer_fintype fun n hn => ?_
      obtain ⟨_, ⟨m, hm, rfl⟩, rfl⟩ := hn
      refine ⟨_, ⟨⟨b, hb⟩ * m * ⟨b, hb⟩⁻¹, hN.conj_mem m hm ⟨b, hb⟩, rfl⟩, ?_⟩
      simp
    obtain ⟨g, hg⟩ := G443J4.L52.le_conj_M4_of_twoLocal hTL ((N.map B.subtype).map φ)
      (IsPGroup.of_card hcN₁) hne hNB (by rw [hcB, hcB']; norm_num)
    refine ⟨(MulAut.conj g⁻¹).toMonoidHom.comp φ, (MulAut.conj g⁻¹).bijective.comp hφ,
      Or.inr ?_⟩
    rw [← Subgroup.map_map]
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨m, hm, rfl⟩ := hg hy
      have e1 : (MulAut.conj g⁻¹).toMonoidHom ((MulAut.conj g).toMonoidHom m) = m := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [e1]
      exact hm
    · rw [G443J4.L52.card_map_conj, hcB, hcB', CFSG.Quasithin.J4M4Card.card_M4]

theorem j4BlockFacts_of_tl
    (hTL : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) : J4BlockFacts := by
  intro K _ _ hK B _ hE
  obtain ⟨f, hfb, hf | hf⟩ := exists_hom_map_eq_tl hTL hK B hE
  · have h := blockConcl_Hj
    rw [← hf] at h
    exact blockConcl_of_bijective f hfb h
  · have h := blockConcl_M4_tl
    rw [← hf] at h
    exact blockConcl_of_bijective f hfb h

end CFSG.Quasithin.H13.Ch4.J4Blk

namespace CFSG.Quasithin.H13.Ch4.J4NSD

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank

attribute [local instance] J4Blk.finite_J

theorem j4L5BlockNotSelfDual_of_tl
    (hTL : CFSG.Quasithin.KGJ4.J4TwoLocalsKW) : J4L5BlockNotSelfDual := by
  intro G _ _ K B hK hBK hS hE v hv hvV hLE e y hy U hU
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup ↥K := B.subgroupOf K with hXdef
  have hXB : X.map K.subtype = B := by
    rw [hXdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left hBK]
  have hEX : IsExt ↥X (fun N _ => IsE2 10 N) (fun Y _ => IsPSL 5 2 1 Y) :=
    NoJ4.isExt_of_mulEquiv ((X.equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hXB)) (NoJ4.isE2_of_mulEquiv 10) (NoJ4.isPSL_of_mulEquiv 5 2 1) hE
  obtain ⟨f, hf, hfX⟩ := J4Blk.exists_hom_map_eq_tl hTL hK X (Or.inr hEX)
  have hcB : Nat.card ↥B = 10239344640 := by
    obtain ⟨N, hN, hNE, hNQ⟩ := hE
    have hcN : Nat.card N = 2 ^ 10 := by
      obtain ⟨e'⟩ := hNE
      rw [Nat.card_congr e'.toEquiv]
      simp
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, F420.card_of_l52 hNQ, hcN]
    norm_num
  have hcX : Nat.card ↥X = Nat.card ↥B := by
    rw [← hXB, Subgroup.card_map_of_injective K.subtype_injective]
  have hXM : X.map f = CFSG.Quasithin.KGJ4.M4 := by
    rcases hfX with h | h
    · exfalso
      have h1 : Nat.card ↥(X.map f) = Nat.card ↥X := Subgroup.card_map_of_injective hf.1
      rw [h, card_Hj j4Facts, hcX, hcB] at h1
      norm_num at h1
    · exact h
  have hQK : (pCoreOf 2 X).map K.subtype = pCoreOf 2 B := by
    have h1 := NoJ4.blockQ_map K.subtype K.subtype_injective X
    rwa [hXB] at h1
  have hQf : (pCoreOf 2 X).map f = F4 j4Facts.mat chkF_true := by
    have h1 := NoJ4.blockQ_map f hf.1 X
    rw [hXM] at h1
    exact h1.trans (pCoreOf_M4 j4Facts.mat chkF_true CFSG.Quasithin.J4M4Card.card_M4)
  have hvK : ∀ i, v i ∈ K := fun i =>
    hBK (pCoreOf_le 2 B (by rw [← hvV]; exact mem_eSub hv i))
  set v' : Fin 10 → ↥K := fun i => ⟨v i, hvK i⟩ with hv'def
  have hv' : EBasis v' := eBasis_of_map K.subtype_injective hv
  have hw : EBasis fun i => f (v' i) := hv'.map hf.1
  have hsub' : eSub hv' = pCoreOf 2 X := by
    apply Subgroup.map_injective K.subtype_injective
    rw [eSub_map hv' K.subtype_injective, hQK]
    exact hvV
  have hsubw : eSub (fJ_basis j4Facts.mat chkF_true) = eSub hw := by
    rw [← eSub_map hv' hf.1, hsub', hQf]
  obtain ⟨P, Q, hPQ, hQP, hPQg⟩ := exists_basis_change (fJ_basis j4Facts.mat chkF_true) hw hsubw
  have hφ : ∀ b : ↥B, (f.comp (Subgroup.inclusion hBK)) b ∈ CFSG.Quasithin.KGJ4.M4 :=
    fun b => by
      rw [← hXM]
      exact ⟨⟨b, hBK b.2⟩, Subgroup.mem_subgroupOf.mpr b.2, rfl⟩
  set ρ : ↥B →* ↥(StatedSL 5 (ZMod 2)) := (piM4 j4Facts.mat chkF_true).comp
    ((f.comp (Subgroup.inclusion hBK)).codRestrict CFSG.Quasithin.KGJ4.M4 hφ) with hρ
  have hmat : ∀ b : ↥B, eMat hv ⟨b, hLE b.2⟩ = Q * psiMat (ρ b) * P := by
    intro b
    obtain ⟨hb', e1⟩ := exists_eMat_comap hv' K.subtype_injective ⟨b, hBK b.2⟩ (hLE b.2)
    obtain ⟨hb'', e2⟩ := exists_eMat_map hv' hf.1 ⟨b, hBK b.2⟩ hb'
    obtain ⟨hJ, e3⟩ := piM4_pairF j4Facts.mat chkF_true ⟨f ⟨b, hBK b.2⟩, hφ b⟩
    have e4 := hPQg (f ⟨b, hBK b.2⟩) hJ hb''
    have e5 : eMat (fJ_basis j4Facts.mat chkF_true) ⟨f ⟨b, hBK b.2⟩, hJ⟩ = psiMat (ρ b) :=
      congrArg Units.val e3
    calc eMat hv ⟨b, hLE b.2⟩ = eMat hv' ⟨⟨b, hBK b.2⟩, hb'⟩ := e1.symm
      _ = eMat hw ⟨f ⟨b, hBK b.2⟩, hb''⟩ := e2.symm
      _ = Q * psiMat (ρ b) * P := by rw [e4, e5]
  have hρker : ∀ b : ↥B, ρ b = 1 ↔ (b : G) ∈ pCoreOf 2 B := by
    intro b
    constructor
    · intro h1
      have h2 : eMat hv ⟨b, hLE b.2⟩ = 1 := by rw [hmat, h1, psiMat_one, Matrix.mul_one, hQP]
      have h3 := (eMat_eq_one_iff hv ⟨b, hLE b.2⟩).mp h2
      rw [hvV] at h3
      exact hS.2.1 ⟨b.2, h3⟩
    · intro h1
      apply psiMat_eq_one
      have h2 : eMat hv ⟨b, hLE b.2⟩ = 1 := by
        rw [eMat_eq_one_iff, Subgroup.mem_centralizer_iff]
        intro x hx
        exact eSub_comm hv x b hx (by rw [hvV]; exact h1)
      have h3 := hmat b
      rw [h2] at h3
      have h4 : P * (Q * psiMat (ρ b) * P) * Q = psiMat (ρ b) := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPQ, Matrix.one_mul, Matrix.mul_assoc, hPQ,
          Matrix.mul_one]
      rw [← h4, ← h3, Matrix.mul_one, hPQ]
  have hker : CFSG.pCore 2 ↥B ≤ ρ.ker := fun b hb =>
    (hρker b).mpr ((mem_pCore_iff_mem_pCoreOf b).mp hb)
  have hord : orderOf (ρ y) = 31 := by
    have hinj : Function.Injective (QuotientGroup.lift (CFSG.pCore 2 ↥B) ρ hker) := by
      rw [injective_iff_map_eq_one]
      intro q hq
      obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective q
      rw [QuotientGroup.lift_mk] at hq
      exact (QuotientGroup.eq_one_iff b).mpr
        ((mem_pCore_iff_mem_pCoreOf b).mpr ((hρker b).mp hq))
    have h1 : ρ y = QuotientGroup.lift (CFSG.pCore 2 ↥B) ρ hker (y : ModO2 B) :=
      (QuotientGroup.lift_mk _ _ _).symm
    rw [h1, orderOf_injective _ hinj, hy, MulEquiv.orderOf_eq, orderOf_singer5]
  set Pg : GL (Fin 10) (ZMod 2) := ⟨P, Q, hPQ, hQP⟩ with hPg
  have hA : eGL hv (Subgroup.inclusion hLE y) = Pg⁻¹ * J4M4.psi (ρ y) * Pg := by
    apply Units.ext
    rw [eGL_coe, Units.val_mul, Units.val_mul, psi_coe]
    exact hmat y
  have hAinv : eGL hv (Subgroup.inclusion hLE y⁻¹) = (eGL hv (Subgroup.inclusion hLE y))⁻¹ := by
    rw [← map_inv, ← map_inv]
  rw [hAinv, hA] at hU
  apply psi_ne_conj_inv hord (Pg * U * Pg⁻¹)
  calc J4M4.psi (ρ y) = Pg * (Pg⁻¹ * J4M4.psi (ρ y) * Pg) * Pg⁻¹ := by group
    _ = Pg * (U * (Pg⁻¹ * J4M4.psi (ρ y) * Pg)⁻¹ * U⁻¹) * Pg⁻¹ := by rw [← hU]
    _ = Pg * U * Pg⁻¹ * (J4M4.psi (ρ y))⁻¹ * (Pg * U * Pg⁻¹)⁻¹ := by group

end CFSG.Quasithin.H13.Ch4.J4NSD
