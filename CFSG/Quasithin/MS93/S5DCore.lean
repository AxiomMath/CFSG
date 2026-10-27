module

public import CFSG.Quasithin.MS93.S51Main

public section

namespace CFSG.Quasithin.MS93.S5D

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise
open S51

section Core

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem commutator_le_Z0q_of_conf (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {Zb : Subgroup (MSP.Sp4 F)} (hZ : Zb = ⊥ ∨ Zb = MSP.X₂ F) {K : Subgroup G} (hKT : K ≤ T)
    (hJ : S5.imSp a K = Zb ⊔ MSP.xPoint (pE₂ F))
    (hJeq : K = S5.liftT T a (Zb ⊔ MSP.xPoint (pE₂ F)))
    (hthom : thompsonJ T ≤ K) (hbaum : baum T ≤ K)
    (hJX : ¬ S5.imSp a (thompsonJ T) ≤ MSP.X₂ F) :
    ⁅pCoreOf 2 M, L⁆ ≤ Z0q M T := by
  classical
  have := hd.charP
  have hl := (S5.sp4Lift G M T L h k F _ _ a hd).2.2
  obtain ⟨nv⟩ := hd.nonempty_natVec
  set J := K with hJdef
  set Jb := Zb ⊔ MSP.xPoint (pE₂ F) with hJbdef
  set Fb := Zb ⊔ MSP.lev₂ F with hFbdef
  set Q := pCoreOf 2 M with hQdef
  have hZX : Zb ≤ MSP.X₂ F := by rcases hZ with h' | h' <;> simp [h']
  have hJT : J ≤ T := hKT
  have hJM : J ≤ M := hJT.trans h.le
  have hJ2 : IsPGroup 2 J := h.isPGroup.to_le hJT
  have hQJ : Q ≤ J := by rw [hJeq]; exact hd.pCoreOf_le_liftT h _
  have hQ2 : IsPGroup 2 Q := h.isPGroup.to_le h.pCore_le
  have hJbFb : Jb ≤ Fb := sup_le_sup_left xPoint_pE₂_le_lev₂ Zb
  have hFbP₂ : Fb ≤ MSP.P₂ F :=
    sup_le (hZX.trans (MSP.X₂_le_Q₂.trans MSP.Q₂_le_P₂)) MSP.lev₂_le_P₂
  have hxBarFb : xBar F ∈ Fb := Subgroup.mem_sup_right xBar_mem_lev₂
  have hUZ : Uq M T L ≤ Z0q M T := Uq_le_Z0q h.L_le
  have hUQ : Uq M T L ≤ Q := hUZ.trans h.Z0q_le_pCoreOf
  let 𝒴 : Set (Subgroup G) := {Y | J ≤ Y ∧ Y ≤ M ∧ S5.imSp a Y = Fb}
  have hY₀ : (Fb.comap a).map M.subtype ∈ 𝒴 := by
    refine ⟨fun j hj => mem_comap_map.2 ⟨hJM hj, hJbFb ?_⟩, Subgroup.map_subtype_le _, ?_⟩
    · rw [← hJ]
      exact S5.mem_imSp.2 ⟨j, hj, hJM hj, rfl⟩
    · rw [S5.imSp, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective
        M.subtype_injective, Subgroup.map_comap_eq_self_of_surjective hd.surj]
  obtain ⟨P, ⟨hJP, hPM, hPa⟩, hPmin⟩ := Set.exists_min_image 𝒴 (fun Y => Nat.card Y)
    (Set.toFinite _) ⟨_, hY₀⟩
  have hQP : Q ≤ P := hQJ.trans hJP
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) := hPM.trans (le_normalizer_pCoreOf M)
  have hxBarP : xBar F ∈ S5.imSp a P := hPa ▸ hxBarFb
  have hPFb : ∀ p (hp : p ∈ P), a ⟨p, hPM hp⟩ ∈ Fb := fun p hp =>
    hPa ▸ S5.mem_imSp.2 ⟨p, hp, hPM hp, rfl⟩
  have hsyl : IsSylowTwoOf J P := isSylowTwoOf_of_max hJP hJ2 fun S hS2 hJS hSP => by
    have hSM := hSP.trans hPM
    refine le_of_isPGroup_of_imSp_le hd h hQJ hJS hSM hS2 ?_
    rw [hJ]
    have hS2' : IsPGroup 2 (S5.imSp a S) :=
      (hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSM).symm).map a
    have h1 : Zb ⊔ MSP.xPoint (pE₂ F) ≤ S5.imSp a S := by
      rw [← hJbdef, ← hJ]; exact S5.imSp_mono a hJS
    have h2 : S5.imSp a S ≤ Zb ⊔ MSP.lev₂ F := by
      rw [← hFbdef, ← hPa]; exact S5.imSp_mono a hSP
    exact (eq_Jbar_of_isPGroup hZX hS2' h1 h2).le
  have hnn : ¬ (J.subgroupOf P).Normal := by
    intro hn
    have hPN : P ≤ Subgroup.normalizer (J : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hJP).1 hn
    have := imSp_le_normalizer (a := a) hPN hxBarP
    rw [hJ] at this
    exact xBar_not_mem_normalizer hZX this
  set Mx := P ⊓ ((Subgroup.normalizer (Jb : Set (MSP.Sp4 F))).comap a).map M.subtype with hMx
  have hSM : J ≤ Mx := by
    refine le_inf hJP fun j hj => mem_comap_map.2 ⟨hJM hj, ?_⟩
    have : a ⟨j, hJM hj⟩ ∈ Jb := hJ ▸ S5.mem_imSp.2 ⟨j, hj, hJM hj, rfl⟩
    exact Subgroup.le_normalizer this
  have hMP : ¬ P ≤ Mx := by
    intro hle
    apply xBar_not_mem_normalizer hZX
    obtain ⟨p, hp, hpM, hpa⟩ := S5.mem_imSp.1 hxBarP
    obtain ⟨hpM', hpN⟩ := mem_comap_map.1 (hle hp).2
    rw [← hpa]
    exact hpN
  have hmax : ∀ Y : Subgroup G, J ≤ Y → Y < P → Y ≤ Mx := by
    intro Y hJY hYP
    have hYM : Y ≤ M := hYP.le.trans hPM
    have h1 : Zb ⊔ MSP.xPoint (pE₂ F) ≤ S5.imSp a Y := by
      rw [← hJbdef, ← hJ]; exact S5.imSp_mono a hJY
    have h2 : S5.imSp a Y ≤ Zb ⊔ MSP.lev₂ F := by
      rw [← hFbdef, ← hPa]; exact S5.imSp_mono a hYP.le
    rcases le_normalizer_or_eq_Fbar hZX h1 h2 with hN | hE
    · intro y hy
      exact ⟨hYP.le hy, mem_comap_map.2 ⟨hYM hy, hN (S5.mem_imSp.2 ⟨y, hy, hYM hy, rfl⟩)⟩⟩
    · exfalso
      have h1 := hPmin Y ⟨hJY, hYM, hE⟩
      exact absurd h1 (not_le.2 (Subgroup.card_lt_of_lt hYP))
  set V : Subgroup G := ((AddSubgroup.toSubgroup (W₀ F).toAddSubgroup).comap nv.toVec).map
    (Uq M T L).subtype with hVdef
  have hmemV : ∀ g : G, g ∈ V ↔ ∃ hg : g ∈ Uq M T L, nv.vec ⟨g, hg⟩ ∈ W₀ F := by
    intro g
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.2, hu⟩
    · rintro ⟨hg, hv⟩
      exact ⟨⟨g, hg⟩, hv, rfl⟩
  have hVU : V ≤ Uq M T L := Subgroup.map_subtype_le _
  have hVP : V ≤ P := hVU.trans (hUQ.trans hQP)
  have hPW : ∀ p (hp : p ∈ P), ∀ w ∈ W₀ F, MSP.mat (a ⟨p, hPM hp⟩) *ᵥ w ∈ W₀ F :=
    fun p hp _ hw => MSP.mulVec_mem_of_mem_stab (Fb_le_stab_W₀ hZX (hPFb p hp)) hw
  have hPV : P ≤ Subgroup.normalizer (V : Set G) := by
    have key : ∀ p ∈ P, ∀ v ∈ V, p * v * p⁻¹ ∈ V := by
      intro p hp v hv
      obtain ⟨hvU, hvW⟩ := (hmemV v).1 hv
      have hpU : p * v * p⁻¹ ∈ Uq M T L :=
        (Subgroup.mem_normalizer_iff.1 (hd.nat.1 (hPM hp)) v).1 hvU
      refine (hmemV _).2 ⟨hpU, ?_⟩
      rw [nv.vec_conj ⟨p, hPM hp⟩ ⟨v, hvU⟩ hpU]
      exact hPW p hp _ hvW
    intro p hp
    rw [Subgroup.mem_normalizer_iff]
    intro v
    exact ⟨key p hp v, fun hv => by simpa [mul_assoc] using key p⁻¹ (P.inv_mem hp) _ hv⟩
  let aP : ↥P →* ↥(MSP.P₂ F) :=
    (a.comp (Subgroup.inclusion hPM)).codRestrict (MSP.P₂ F) fun x => hFbP₂ (hPFb x x.2)
  let ϱ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) F := MSP.levQ.comp aP
  have hϱmat : ∀ x : ↥P, (ϱ x : Matrix (Fin 2) (Fin 2) F) = MSP.levMat (a ⟨x, hPM x.2⟩) :=
    fun x => rfl
  have hϱ : Function.Surjective ϱ := by
    intro A
    have hlev : MSP.levHom₂ A ∈ S5.imSp a P := by
      rw [hPa]
      exact Subgroup.mem_sup_right (by rw [← MSP.range_levHom₂]; exact ⟨A, rfl⟩)
    obtain ⟨p, hp, hpM, hpa⟩ := S5.mem_imSp.1 hlev
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Subtype.ext
    rw [hϱmat]
    show MSP.levMat (a ⟨p, hpM⟩) = _
    rw [hpa, MSP.levMat_levHom₂]
  let π : MSP.V4 F →+ (Fin 2 → F) :=
    { toFun := fun v => ![v (.inl 1), v (.inr 1)]
      map_zero' := by funext i; fin_cases i <;> rfl
      map_add' := fun v w => by funext i; fin_cases i <;> rfl }
  let ψ : ↥V →* Multiplicative (Fin 2 → F) :=
    (AddMonoidHom.toMultiplicative π).comp (nv.toVec.comp (Subgroup.inclusion hVU))
  have hψapply : ∀ v : ↥V, Multiplicative.toAdd (ψ v) =
      ![nv.vec ⟨v, hVU v.2⟩ (.inl 1), nv.vec ⟨v, hVU v.2⟩ (.inr 1)] := fun v => rfl
  have hψ : Function.Surjective ψ := by
    intro y
    set w : MSP.V4 F := Multiplicative.toAdd y 0 • MSP.e₂ F + Multiplicative.toAdd y 1 • MSP.f₂ F
      with hw
    obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd w)
    have hvu : nv.vec u = w := by rw [S5.NatVec.vec, hu]; rfl
    have huV : (u : G) ∈ V := (hmemV _).2 ⟨u.2, by
      rw [mem_W₀, show (⟨(u : G), u.2⟩ : ↥(Uq M T L)) = u from rfl, hvu, hw]
      simp⟩
    refine ⟨⟨u, huV⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    rw [hψapply, show (⟨((⟨(u : G), huV⟩ : ↥V) : G), hVU huV⟩ : ↥(Uq M T L)) = u from rfl, hvu,
      hw]
    funext i
    fin_cases i <;> simp
  have hψϱ : ∀ (p : ↥P) (v v' : ↥V), (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψ v') =
        (ϱ p : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd (ψ v)) := by
    intro p v v' hv'
    obtain ⟨_hvU, hvW⟩ := (hmemV v).1 v.2
    have hvW' := mem_W₀.1 hvW
    have h1 := nv.equiv ⟨p, hPM p.2⟩ ⟨v, hVU v.2⟩ ⟨v', hVU v'.2⟩ hv'
    obtain ⟨c1, c2⟩ := mulVec_coords (a ⟨p, hPM p.2⟩) hvW'.1 hvW'.2
    rw [hψapply, hψapply, hϱmat]
    have e1 : nv.vec ⟨v', hVU v'.2⟩ = MSP.mat (a ⟨p, hPM p.2⟩) *ᵥ nv.vec ⟨v, hVU v.2⟩ := h1
    rw [e1, c1, c2]
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hoddL : Setup.oddOrderSubgroup P ≤ L := by
    refine (Subgroup.closure_le L).2 ?_
    rintro x ⟨hxP, hodd⟩
    exact S5.mem_L_of_odd h (hPM hxP) hodd (pow_orderOf_eq_one x)
  obtain ⟨x₀, hx₀P, hx₀M, hx₀odd, hx₀a⟩ := exists_odd_imSp_xBar hxBarP
  have hx₀O : x₀ ∈ Setup.oddOrderSubgroup P := Subgroup.subset_closure ⟨hx₀P, hx₀odd⟩
  have hfix0 : ∀ w ∈ W₀ F, MSP.mat (a ⟨x₀, hx₀M⟩) *ᵥ w = w → w = 0 := by
    intro w hw hfw
    have hfx : MSP.mat (xBar F) *ᵥ w = w := by
      rcases hx₀a with h' | h'
      · rwa [h'] at hfw
      · rw [h'] at hfw
        calc MSP.mat (xBar F) *ᵥ w = MSP.mat (xBar F) *ᵥ (MSP.mat (xBar F)⁻¹ *ᵥ w) := by
              rw [hfw]
          _ = w := MSP.mat_mulVec_inv _ _
    have hw' := mem_W₀.1 hw
    rw [xBar_mulVec] at hfx
    have e2 := congrFun hfx (.inl 1)
    have e4 := congrFun hfx (.inr 1)
    simp [hw'.1, hw'.2] at e2 e4
    refine MSP.ext4 ?_ ?_ ?_ ?_
    · simpa using hw'.1
    · simp
      linear_combination e4
    · simpa using hw'.2
    · simp
      linear_combination e2 + e4
  have hψker : ψ.ker =
      (Subgroup.centralizer (Setup.oddOrderSubgroup P : Set G)).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    obtain ⟨_hvU, hvW⟩ := (hmemV v).1 v.2
    have hvW' := mem_W₀.1 hvW
    constructor
    · intro hv
      have hvec : nv.vec ⟨v, hVU v.2⟩ = 0 := by
        have h1 := congrArg Multiplicative.toAdd hv
        rw [hψapply] at h1
        refine MSP.ext4 (by simpa using hvW'.1) ?_ (by simpa using hvW'.2) ?_
        · simpa using congrFun h1 0
        · simpa using congrFun h1 1
      have hker : nv.toVec ⟨v, hVU v.2⟩ = 1 := Multiplicative.toAdd.injective hvec
      exact Subgroup.centralizer_le hoddL ((nv.ker_iff _).1 hker).2
    · intro hv
      have hcomm : ((⟨x₀, hx₀M⟩ : ↥M) : G) * ((⟨v, hVU v.2⟩ : ↥(Uq M T L)) : G) =
          ((⟨v, hVU v.2⟩ : ↥(Uq M T L)) : G) * ((⟨x₀, hx₀M⟩ : ↥M) : G) :=
        Subgroup.mem_centralizer_iff.1 hv x₀ hx₀O
      have h0 := hfix0 _ hvW (nv.mat_mulVec_vec_of_commute ⟨x₀, hx₀M⟩ ⟨v, hVU v.2⟩ hcomm)
      apply Multiplicative.toAdd.injective
      rw [hψapply, h0]
      funext i
      fin_cases i <;> rfl
  have hK1 : ∀ c : ↥P, (c : G) ∈ Subgroup.centralizer (V : Set G) → ϱ c = 1 := by
    intro c hc
    refine QuasithinUnique.Setup.Campbell.eq_one_of_forall_smul_vec fun y => ?_
    obtain ⟨v, hv⟩ := hψ (Multiplicative.ofAdd y)
    have hcv : (v : G) = (c : G) * (v : G) * (c : G)⁻¹ := by
      rw [← Subgroup.mem_centralizer_iff.1 hc v v.2, mul_inv_cancel_right]
    have h1 := hψϱ c v v hcv
    rw [hv] at h1
    rw [Matrix.SpecialLinearGroup.smul_def]
    exact h1.symm
  have hK2 : ∀ c : ↥P, ϱ c = 1 → (c : G) ∈ Subgroup.centralizer (V : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨hvU, hvW⟩ := (hmemV v).1 hv
    have hvW' := mem_W₀.1 hvW
    have hcU : (c : G) * v * (c : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hd.nat.1 (hPM c.2)) v).1 hvU
    have hlevM : MSP.levMat (a ⟨c, hPM c.2⟩) = 1 := by
      rw [← hϱmat, hc]
      rfl
    have hvec : nv.vec ⟨_, hcU⟩ = nv.vec ⟨v, hvU⟩ := by
      rw [nv.vec_conj ⟨c, hPM c.2⟩ ⟨v, hvU⟩ hcU]
      obtain ⟨c1, c2⟩ := mulVec_coords (a ⟨c, hPM c.2⟩) hvW'.1 hvW'.2
      have hW := mem_W₀.1 (hPW c c.2 _ hvW)
      refine MSP.ext4 ?_ ?_ ?_ ?_
      · rw [hW.1, hvW'.1]
      · rw [c1, hlevM]
        simp
      · rw [hW.2, hvW'.2]
      · rw [c2, hlevM]
        simp
    have hker : nv.toVec (⟨_, hcU⟩ * (⟨v, hvU⟩ : ↥(Uq M T L))⁻¹) = 1 := by
      rw [map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      have : Multiplicative.toAdd (nv.toVec ⟨_, hcU⟩) = Multiplicative.toAdd (nv.toVec ⟨v, hvU⟩) :=
        hvec
      rw [toAdd_mul, toAdd_inv, this, add_neg_cancel, toAdd_one]
    have h1 := ((nv.ker_iff _).1 hker).2
    have h2 := hl c (hPM c.2) v hvU h1
    calc v * (c : G) = (c : G) * v * (c : G)⁻¹ * c := by rw [h2]
      _ = c * v := by group
  have hVe : IsElemAbelian 2 V := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => h.isElemAbelian_Uq.2 x (hVU hx)⟩
    exact S5.IsSp4Data.commute_of_mem_Uq h (hVU x.2) (hVU y.2)
  have hred : IsTwoReducedIn P V := by
    refine ⟨hVP, hPV, hVe, fun D hDP hPD hD2 => ?_⟩
    set D' := D.subgroupOf P with hD'
    have hD'n : D'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDP).2 hPD
    have hmapn : (D'.map ϱ).Normal := hD'n.map ϱ hϱ
    have hmap2 : IsPGroup 2 (D'.map ϱ) := by
      rintro ⟨_, ⟨d, hd, rfl⟩⟩
      obtain ⟨e, he⟩ := hD2 d (Subgroup.mem_subgroupOf.1 hd)
      refine ⟨e, Subtype.ext ?_⟩
      have := hK1 (d ^ 2 ^ e) (by simpa using he)
      simp [← map_pow, this]
    have hbot := eq_bot_of_normal_isPGroup_sl2 _ hmap2
    intro d hd
    have h1 : ϱ ⟨d, hDP hd⟩ ∈ D'.map ϱ := ⟨⟨d, hDP hd⟩, Subgroup.mem_subgroupOf.2 hd, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    exact hK2 ⟨d, hDP hd⟩ h1
  have hchar : CharTwo P := by
    intro x hx
    have hQO : Q ≤ pCoreOf 2 P :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQP hPQ hQ2
    exact hQO (h.charTwo ⟨hPM hx.1, Subgroup.centralizer_le hQO hx.2⟩)
  have hthomJ : thompsonJ J = thompsonJ T := B6.thompsonJ_eq_of_le hthom hJT
  have hJ' : ⁅thompsonJ J, V⁆ ≠ ⊥ := by
    rw [hthomJ]
    intro hbot
    apply hJX
    rintro _ ⟨x, hx, rfl⟩
    have hxT : (x : G) ∈ thompsonJ T := Subgroup.mem_subgroupOf.1 hx
    have hxJ : (x : G) ∈ J := hthom hxT
    have hyJb : a x ∈ Jb := by
      rw [← hJ]
      exact ⟨x, Subgroup.mem_subgroupOf.2 hxJ, rfl⟩
    have hyX : a x ∈ MSP.X₂ F ⊔ MSP.xPoint (pE₂ F) := sup_le_sup_right hZX _ hyJb
    have hN : MSP.X₂ F ≤ Subgroup.normalizer (MSP.xPoint (pE₂ F) : Set (MSP.Sp4 F)) := by
      intro z hz
      rw [Subgroup.mem_normalizer_iff]
      intro w
      have hcz : ∀ w ∈ MSP.xPoint (pE₂ F), z * w * z⁻¹ = w := fun w hw => by
        rw [MSP.Q₁_comm (MSP.X₂_le_Q₁ hz) (MSP.xPoint_le_qLine MSP.isLine_ln₀ pE₂_le_ln₀ hw),
          mul_inv_cancel_right]
      constructor
      · intro hw
        rw [hcz w hw]
        exact hw
      · intro hw
        have hc := MSP.Q₁_comm (MSP.X₂_le_Q₁ hz)
          (MSP.xPoint_le_qLine MSP.isLine_ln₀ pE₂_le_ln₀ hw)
        have hw' : w = z * w * z⁻¹ := by
          calc w = z⁻¹ * ((z * w * z⁻¹) * z) := by group
            _ = z⁻¹ * (z * (z * w * z⁻¹)) := by rw [hc]
            _ = z * w * z⁻¹ := by group
        rw [hw']
        exact hw
    have hy' : a x ∈ ((MSP.X₂ F ⊔ MSP.xPoint (pE₂ F) : Subgroup (MSP.Sp4 F)) :
        Set (MSP.Sp4 F)) := hyX
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hy'
    obtain ⟨z, hz, t, ht, hzt⟩ := hy'
    replace hzt : z * t = a x := hzt
    by_contra hyX2
    have ht1 : t ≠ 1 := fun h1 => hyX2 (by rw [← hzt, h1, mul_one]; exact hz)
    obtain ⟨c, rfl⟩ := (MSP.mem_xPoint_span MSP.e₂_ne_zero).1 ht
    have hc0 : c ≠ 0 := fun h0 => ht1 (by rw [h0, MSP.transv_zero])
    have hyf : MSP.mat (a x) *ᵥ MSP.f₂ F = MSP.f₂ F + c • MSP.e₂ F := by
      have hmem : MSP.f₂ F + c • MSP.e₂ F ∈ MSP.perp (MSP.pt₀ F) := by
        rw [MSP.pt₀_eq_span, MSP.mem_perp_span, MSP.form_e₁]
        simp
      rw [← hzt, MSP.mat_mul_mulVec, MSP.transv_mulVec, MSP.form_e₂]
      have hf : (MSP.f₂ F) (.inr 1) = 1 := by simp
      rw [hf, mul_one]
      exact MSP.mem_fixer.1 hz _ hmem
    obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd (MSP.f₂ F))
    have hvu : nv.vec u = MSP.f₂ F := by rw [S5.NatVec.vec, hu]; rfl
    have huV : (u : G) ∈ V := (hmemV _).2 ⟨u.2, by
      rw [mem_W₀, show (⟨(u : G), u.2⟩ : ↥(Uq M T L)) = u from rfl, hvu]
      simp⟩
    have hcomm : ((x : ↥M) : G) * (u : G) = (u : G) * x := by
      have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot hxT
      exact (Subgroup.mem_centralizer_iff.1 this _ huV).symm
    have hfix := nv.mat_mulVec_vec_of_commute x u hcomm
    rw [hvu, hyf] at hfix
    have : c • MSP.e₂ F = 0 := by
      have := congrArg (· - MSP.f₂ F) hfix
      simpa using this
    have h2 := congrFun this (.inl 1)
    simp at h2
    exact hc0 h2
  have hbJ : baum T = baum J := baum_eq_of_le hbaum hJT
  have hnc : ∀ C : Subgroup G, C ≤ baum J → C ≠ ⊥ → (C.subgroupOf (baum J)).Characteristic →
      ¬ Setup.oddOrderSubgroup P ⊔ baum J ≤ Subgroup.normalizer (C : Set G) := by
    intro C hCb hC1 hCc hN
    have hbT : baum J ≤ T := hbJ ▸ (inf_le_left : baum T ≤ T)
    have hCT : (C.subgroupOf T).Characteristic := C1GN.characteristic_subgroupOf_trans hbT hCb
      (hbJ ▸ C1GN.characteristic_baum T) hCc
    have hCJ : (C.subgroupOf J).Characteristic := C1GN.characteristic_subgroupOf_trans
      inf_le_left hCb (C1GN.characteristic_baum J) hCc
    have hTN : T ≤ Subgroup.normalizer (C : Set G) :=
      Subgroup.le_normalizer.trans (normalizer_le_of_char (hCb.trans hbT) hCT)
    have hJN : Subgroup.normalizer (J : Set G) ≤ Subgroup.normalizer (C : Set G) :=
      normalizer_le_of_char (hCb.trans inf_le_left) hCJ
    set Yb := S5.imSp a (Subgroup.normalizer (C : Set G) ⊓ M) with hYb
    have hNJb : Subgroup.normalizer (Jb : Set (MSP.Sp4 F)) ≤ Yb := by
      have := normalizer_le_imSp hd h hJM hJ2 hQJ
      rw [hJ] at this
      exact this.trans (S5.imSp_mono a (inf_le_inf_right M hJN))
    have hxY : a ⟨x₀, hx₀M⟩ ∈ Yb :=
      S5.mem_imSp.2 ⟨x₀, ⟨hN (Subgroup.mem_sup_left hx₀O), hx₀M⟩, hx₀M, rfl⟩
    have hopp : MSP.form F (MSP.e₂ F) (MSP.mat (a ⟨x₀, hx₀M⟩) *ᵥ MSP.e₂ F) ≠ 0 := by
      rcases hx₀a with h' | h'
      · rw [h']; exact form_e₂_xBar
      · rw [h']; exact form_e₂_xBar_inv
    have hQY : MSP.qPoint (pE₂ F) ≤ Yb := by
      rcases hZ with hZ0 | hZ2
      · have hJb0 : Jb = MSP.xPoint (pE₂ F) := by rw [hJbdef, hZ0, bot_sup_eq]
        refine le_trans ?_ hNJb
        rw [hJb0, MSP.normalizer_xPoint isPoint_pE₂]
        exact (MSP.qPoint_le_fixer _).trans (MSP.fixer_le_stab _)
      · have hQ₁ : MSP.Q₁ F ≤ Yb := (Q₁_le_normalizer (Jbar_le_Q₁ hZX)).trans hNJb
        have hw : MSP.wAlpha F ∈ Yb := hNJb (by rw [hJbdef, hZ2]; exact wAlpha_mem_normalizer)
        refine qPoint_pE₂_le hQ₁ hw hxY ?_ ?_
        · rcases hx₀a with h' | h'
          · rw [h', xBar_mulVec_e₁]
          · rw [h']
            calc MSP.mat (xBar F)⁻¹ *ᵥ MSP.e₁ F =
                MSP.mat (xBar F)⁻¹ *ᵥ (MSP.mat (xBar F) *ᵥ MSP.e₁ F) := by rw [xBar_mulVec_e₁]
              _ = MSP.e₁ F := MSP.mat_inv_mulVec _ _
        · rcases hx₀a with h' | h'
          · rw [h', xBar_mulVec_e₂, MSP.mem_ln₀]
            simp
          · rw [h', xBar_inv_mulVec_e₂, MSP.mem_ln₀]
            simp
    have htop : Yb = ⊤ := eq_top_of_qPoint_pE₂_le hQY hxY hopp
    have hQC : Q ≤ Subgroup.normalizer (C : Set G) ⊓ M :=
      le_inf (h.pCore_le.trans hTN) (pCoreOf_le' M)
    have hMC := hd.eq_of_imSp_eq h inf_le_right hQC (by rw [← hYb, htop]; exact le_top)
    exact h.noChar C ((hCb.trans hbT)) hC1 hCT (hMC ▸ inf_le_left)
  set X := Q ⊓ Setup.oddOrderSubgroup P with hXdef
  have hPO : P ≤ Subgroup.normalizer (Setup.oddOrderSubgroup P : Set G) :=
    Subgroup.le_normalizer.trans (Setup.normalizer_le_normalizer_oddOrderSubgroup P)
  have hXV : ⁅X, Setup.oddOrderSubgroup P⁆ ≤ V :=
    push_up hsyl hnn hSM hMP hmax hred ϱ hϱ ψ hψ hψϱ hψker hchar hnc hJ'
      (inf_le_right.trans le_sup_left) (hQ2.to_le inf_le_left) (le_normalizer_inf hPQ hPO)
  have hcop : ∀ x ∈ P, Odd (orderOf x) → ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ Z0q M T := by
    intro x hxP hodd
    have hxO : x ∈ Setup.oddOrderSubgroup P := Subgroup.subset_closure ⟨hxP, hodd⟩
    obtain ⟨r, hr⟩ := hQ2.exists_card_eq
    refine EmptyFaithfulMultiple.L3213.commutator_mem_of_series_coprime (B := X) (D := Q)
      (m := orderOf x) (n := Nat.card Q) ?_ (pow_orderOf_eq_one x)
      (le_normalizer_Z0q M T (hPM hxP))
      ((pCoreOf_le' M).trans (le_normalizer_Z0q M T)) inf_le_left ?_ ?_ ?_
    · rw [hr]
      exact Nat.Coprime.pow_right r (Nat.coprime_two_right.2 hodd)
    · intro b hb
      have hb1 : b ^ Nat.card Q = 1 := by
        have := pow_card_eq_one' (G := ↥Q) (x := ⟨b, hb.1⟩)
        exact congrArg Subtype.val this
      rw [hb1]
      exact Subgroup.one_mem _
    · intro d hd
      have hdP : d ∈ P := hQP hd
      refine ⟨?_, ?_⟩
      · have h1 : x * d * x⁻¹ ∈ Q :=
          (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf M (hPM hxP)) d).1 hd
        exact Q.mul_mem h1 (Q.inv_mem hd)
      · have h2 : d * x⁻¹ * d⁻¹ ∈ Setup.oddOrderSubgroup P := by
          refine Subgroup.subset_closure ⟨P.mul_mem (P.mul_mem hdP (P.inv_mem hxP))
            (P.inv_mem hdP), ?_⟩
          have : d * x⁻¹ * d⁻¹ = (MulAut.conj d) x⁻¹ := rfl
          rw [this, MulEquiv.orderOf_eq,
            orderOf_inv]
          exact hodd
        have e : x * d * x⁻¹ * d⁻¹ = x * (d * x⁻¹ * d⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hxO h2
    · intro b hb
      have h1 : ⁅b, x⁆ ∈ ⁅X, Setup.oddOrderSubgroup P⁆ := Subgroup.commutator_mem_commutator hb hxO
      have h2 := hUZ (hVU (hXV h1))
      have e : x * b * x⁻¹ * b⁻¹ = ⁅b, x⁆⁻¹ := by
        rw [commutatorElement_inv, commutatorElement_def]
      rw [e]
      exact (Z0q M T).inv_mem h2
  set K₁ := relCent M Q (Z0q M T) (le_normalizer_Z0q M T) (le_normalizer_pCoreOf M) with hK₁
  have hoddK : Setup.oddOrderSubgroup P ≤ K₁ := by
    refine (Subgroup.closure_le K₁).2 ?_
    rintro x ⟨hxP, hodd⟩
    refine ⟨hPM hxP, fun q hq => ?_⟩
    rw [commutatorElement_def]
    exact hcop x hxP hodd q hq
  have hK₁n : (S5.imSp a K₁).Normal := by
    have : (K₁.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer relCent_le).2 le_normalizer_relCent
    exact this.map a hd.surj
  have hxK : xBar F ∈ S5.imSp a K₁ := by
    have h1 : a ⟨x₀, hx₀M⟩ ∈ S5.imSp a K₁ := S5.mem_imSp.2 ⟨x₀, hoddK hx₀O, hx₀M, rfl⟩
    rcases hx₀a with h' | h'
    · rwa [h'] at h1
    · rw [h'] at h1
      simpa using (S5.imSp a K₁).inv_mem h1
  have hcomm := commutator_le_of_xBar_mem (N := S5.imSp a K₁) hxK
  have hLc : S5.imSp a L ≤ commutator (MSP.Sp4 F) := by
    have hLL : ⁅L, L⁆ ≤ ((commutator (MSP.Sp4 F)).comap a).map M.subtype := by
      rw [Subgroup.commutator_le]
      intro l₁ hl₁ l₂ hl₂
      refine mem_comap_map.2 ⟨Subgroup.commutator_mem_commutator (h.L_le hl₁) (h.L_le hl₂) |>
        fun h' => commutator_le_of_le le_rfl le_rfl h', ?_⟩
      have e : (⟨⁅l₁, l₂⁆, _⟩ : ↥M) = ⁅(⟨l₁, h.L_le hl₁⟩ : ↥M), ⟨l₂, h.L_le hl₂⟩⁆ := rfl
      rw [e, map_commutatorElement, commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rintro _ ⟨x, hx, rfl⟩
    have hxL : (x : G) ∈ ⁅L, L⁆ := by rw [h.perfect]; exact Subgroup.mem_subgroupOf.1 hx
    obtain ⟨hxM, hxc⟩ := mem_comap_map.1 (hLL hxL)
    exact hxc
  have hLK : L ≤ K₁ ⊔ Q :=
    hd.L_le_of_imSp_le h le_sup_right (hLc.trans (hcomm.trans (S5.imSp_mono a le_sup_left)))
  have hLK₁ : L ≤ K₁ :=
    C2Push.le_of_perfect_le_sup hQ2 ((pCoreOf_le' M).trans le_normalizer_relCent) h.perfect hLK
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have := (hLK₁ hl).2 q hq
  rw [← commutatorElement_inv]
  exact (Z0q M T).inv_mem this

omit [Finite G] [Fintype F] in
theorem liftT_conjA (g : MSP.Sp4 F) (A : Subgroup ↥(StatedSp 2 F)) :
    S5.liftT T (conjA g a) (A.map (MulAut.conj g).toMonoidHom) = S5.liftT T a A := by
  ext t
  simp only [S5.mem_liftT, Subgroup.mem_map, conjA_apply]
  constructor
  · rintro ⟨htT, htM, x, hx, hxe⟩
    refine ⟨htT, htM, ?_⟩
    have : x = a ⟨t, htM⟩ := by
      have := congrArg (fun y => g⁻¹ * y * g) hxe
      simpa [MulAut.conj_apply, mul_assoc] using this
    exact this ▸ hx
  · rintro ⟨htT, htM, hA⟩
    exact ⟨htT, htM, _, hA, rfl⟩

theorem thompsonJ_not_le (h : PUHyp M T L) : ¬ thompsonJ T ≤ pCoreOf 2 M := by
  intro hle
  have heq : thompsonJ (pCoreOf 2 M) = thompsonJ T := B6.thompsonJ_eq_of_le hle h.pCore_le
  have := Setup.characteristic_thompsonJ (pCoreOf 2 M)
  have hN := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((thompsonJ (pCoreOf 2 M)).subgroupOf (pCoreOf 2 M))
  rw [Subgroup.map_subgroupOf_eq_of_le (C1GN.thompsonJ_le _), heq] at hN
  exact h.noChar _ (C1GN.thompsonJ_le T) (Setup.thompsonJ_ne_bot h.isPGroup h.ne_bot)
    (Setup.characteristic_thompsonJ T) ((le_normalizer_pCoreOf M).trans hN)

theorem commutator_le_Z0q_of_xPoint (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    {p₁ p₂ : Submodule F (MSP.V4 F)} (hp₁ : MSP.IsPoint p₁) (hp₂ : MSP.IsPoint p₂)
    {K : Subgroup G} (hKT : K ≤ T) (hK : K = S5.liftT T a (MSP.xPoint p₁ ⊔ MSP.xPoint p₂))
    (hJ : S5.imSp a K = MSP.xPoint p₁ ⊔ MSP.xPoint p₂)
    (hthom : thompsonJ T ≤ K) (hbaum : baum T ≤ K) :
    ⁅pCoreOf 2 M, L⁆ ≤ Z0q M T := by
  classical
  have := hd.charP
  have hnotQ := thompsonJ_not_le h
  have hR : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hJT1 : ∀ (b : ↥M →* ↥(StatedSp 2 F)), S5.IsSp4Data M T L k F b →
      S5.imSp b (thompsonJ T) ≠ ⊥ := by
    intro b hb hbot
    apply hnotQ
    intro x hx
    have hxT : x ∈ T := (C1GN.thompsonJ_le T) hx
    have hxk : x ∈ S5.kerG b := by
      refine (S5.mem_kerG b).2 ⟨h.le hxT, ?_⟩
      have : b ⟨x, h.le hxT⟩ ∈ S5.imSp b (thompsonJ T) := S5.mem_imSp.2 ⟨x, hx, h.le hxT, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact this
    rw [← hb.inf_kerG h]
    exact ⟨hxT, hxk⟩
  have hJR : MSP.xPoint p₁ ⊔ MSP.xPoint p₂ ≤ S5.imSp a T := hJ ▸ S5.imSp_mono a hKT
  have hne₀ : MSP.pt₀ F ≠ pE₂ F := by
    intro hpt
    have hm : MSP.e₂ F ∈ MSP.pt₀ F := hpt ▸ Submodule.mem_span_singleton_self _
    have := (MSP.mem_pt₀.1 hm).1
    simp at this
  by_cases he : p₁ = p₂
  ·
    subst he
    obtain ⟨g, hg⟩ := exists_map_pE₂_eq (F := F) hp₁
    have hd' := IsSp4Data.conjA hd g⁻¹
    have hp : p₁.map (Matrix.mulVecLin (MSP.mat g⁻¹)) = pE₂ F := by
      rw [← hg]
      exact MSP.map_map_mat_inv' g _
    have hJ' : S5.imSp (conjA g⁻¹ a) K = ⊥ ⊔ MSP.xPoint (pE₂ F) := by
      rw [imSp_conjA, hJ, sup_idem, MSP.xPoint_map_conj, hp, bot_sup_eq]
    have hJeq'' : K = S5.liftT T (conjA g⁻¹ a) (⊥ ⊔ MSP.xPoint (pE₂ F)) := by
      rw [bot_sup_eq, ← hp, ← MSP.xPoint_map_conj, liftT_conjA, hK, sup_idem]
    refine commutator_le_Z0q_of_conf hd' h (Or.inl rfl) hKT hJ' hJeq'' hthom hbaum ?_
    intro hle
    apply hJT1 _ hd'
    have h1 : S5.imSp (conjA g⁻¹ a) (thompsonJ T) ≤ MSP.xPoint (pE₂ F) := by
      have := S5.imSp_mono (conjA g⁻¹ a) hthom
      rwa [hJ', bot_sup_eq] at this
    have h3 : MSP.X₂ F ⊓ MSP.xPoint (pE₂ F) = ⊥ :=
      S5.xPoint_inf_xPoint MSP.isPoint_pt₀ isPoint_pE₂ hne₀
    rw [← le_bot_iff, ← h3]
    exact le_inf hle h1
  ·
    have hperp : p₂ ≤ MSP.perp p₁ := S5.le_perp_of_xPoint_le hp₁ hp₂ he hR
      (le_sup_left.trans hJR) (le_sup_right.trans hJR)
    have hperp' : p₁ ≤ MSP.perp p₂ := by
      intro x hx
      rw [MSP.mem_perp]
      intro w hw
      rw [MSP.form_swap, neg_eq_zero]
      exact (MSP.mem_perp.1 (hperp hw)) x hx
    have hinf : MSP.xPoint p₁ ⊓ MSP.xPoint p₂ = ⊥ := S5.xPoint_inf_xPoint hp₁ hp₂ he
    obtain ⟨q₁, q₂, hq₁, hq₂, hne, hqperp, hJq, hKq, hJTq⟩ : ∃ q₁ q₂ : Submodule F (MSP.V4 F),
        MSP.IsPoint q₁ ∧ MSP.IsPoint q₂ ∧ q₁ ≠ q₂ ∧ q₂ ≤ MSP.perp q₁ ∧
        S5.imSp a K = MSP.xPoint q₁ ⊔ MSP.xPoint q₂ ∧
        K = S5.liftT T a (MSP.xPoint q₁ ⊔ MSP.xPoint q₂) ∧
        ¬ S5.imSp a (thompsonJ T) ≤ MSP.xPoint q₂ := by
      by_cases h2 : S5.imSp a (thompsonJ T) ≤ MSP.xPoint p₂
      · refine ⟨p₂, p₁, hp₂, hp₁, Ne.symm he, hperp', by rw [hJ, sup_comm],
          by rw [hK, sup_comm], fun h1 => ?_⟩
        apply hJT1 _ hd
        rw [← le_bot_iff, ← hinf]
        exact le_inf h1 h2
      · exact ⟨p₁, p₂, hp₁, hp₂, he, hperp, hJ, hK, h2⟩
    obtain ⟨g, hg₁, hg₂⟩ := exists_map_pE₂_pt₀_eq hq₁ hq₂ hne hqperp
    have hd' := IsSp4Data.conjA hd g⁻¹
    have h1 : q₁.map (Matrix.mulVecLin (MSP.mat g⁻¹)) = pE₂ F := by
      rw [← hg₁]
      exact MSP.map_map_mat_inv' g _
    have h2 : q₂.map (Matrix.mulVecLin (MSP.mat g⁻¹)) = MSP.pt₀ F := by
      rw [← hg₂]
      exact MSP.map_map_mat_inv' g _
    have hmap : (MSP.xPoint q₁ ⊔ MSP.xPoint q₂).map (MulAut.conj g⁻¹).toMonoidHom =
        MSP.X₂ F ⊔ MSP.xPoint (pE₂ F) := by
      rw [Subgroup.map_sup, MSP.xPoint_map_conj, MSP.xPoint_map_conj, h1, h2, sup_comm]
    have hJ' : S5.imSp (conjA g⁻¹ a) K = MSP.X₂ F ⊔ MSP.xPoint (pE₂ F) := by
      rw [imSp_conjA, hJq, hmap]
    have hJeq' : K = S5.liftT T (conjA g⁻¹ a) (MSP.X₂ F ⊔ MSP.xPoint (pE₂ F)) := by
      rw [← hmap, liftT_conjA, hKq]
    refine commutator_le_Z0q_of_conf hd' h (Or.inr rfl) hKT hJ' hJeq' hthom hbaum ?_
    intro hle
    apply hJTq
    have hX : MSP.X₂ F = (MSP.xPoint q₂).map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [MSP.xPoint_map_conj, h2]
    rw [imSp_conjA, hX] at hle
    exact (Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj g⁻¹).toMonoidHom)
      (MulAut.conj g⁻¹).injective).1 hle

theorem false_of_xPoint (hd : S5.IsSp4Data M T L k F a) (h : PUHyp M T L)
    (hb : 2 < critDist (puAmalgam h.le)) {p₁ p₂ : Submodule F (MSP.V4 F)}
    (hp₁ : MSP.IsPoint p₁) (hp₂ : MSP.IsPoint p₂) {K : Subgroup G} (hKT : K ≤ T)
    (hK : K = S5.liftT T a (MSP.xPoint p₁ ⊔ MSP.xPoint p₂))
    (hKa : S5.imSp a K = MSP.xPoint p₁ ⊔ MSP.xPoint p₂)
    (hthom : thompsonJ T ≤ K) (hbaum : baum T ≤ K) : False :=
  false_of_commutator_le_Z0q h hb
    (commutator_le_Z0q_of_xPoint hd h hp₁ hp₂ hKT hK hKa hthom hbaum)

end Core

end CFSG.Quasithin.MS93.S5D
