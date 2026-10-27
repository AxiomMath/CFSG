module

public import CFSG.Quasithin.Vol2.Ch7Lem776c
public import CFSG.Quasithin.Background.HSL3S77Trans

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem centralizer_conj_eq (g u : G) :
    Subgroup.centralizer ({g * u * g⁻¹} : Set G) =
      (Subgroup.centralizer ({u} : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * u * g⁻¹ * x) * g := by rw [h]
      _ = u * (g⁻¹ * x * g) := by group
  · intro h
    calc x * (g * u * g⁻¹) = g * (g⁻¹ * x * g * u) * g⁻¹ := by group
      _ = g * (u * (g⁻¹ * x * g)) * g⁻¹ := by rw [h]
      _ = g * u * g⁻¹ * x := by group

omit [Finite G] in
theorem charTwo_centralizer_conj (g u : G) :
    CharTwo (Subgroup.centralizer ({g * u * g⁻¹} : Set G)) ↔
      CharTwo (Subgroup.centralizer ({u} : Set G)) := by
  rw [centralizer_conj_eq]
  exact charTwo_map_equiv_iff (MulAut.conj g) _

theorem mem_V₁_iff_vp {p : PairMod (ZMod 2)} : p ∈ V₁ (ZMod 2) ↔ (vp p).2 = 0 := by
  rw [mem_V₁]
  constructor
  · intro h
    change Multiplicative.toAdd p.2 = 0
    rw [h, toAdd_one]
  · intro h
    exact Multiplicative.toAdd.injective (h.trans toAdd_one.symm)

theorem rho_th0_pow_three : (SL3One.rho th0) ^ 3 = 1 := by
  rw [← map_pow, th0_pow_three, map_one]

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem vec_mem_I_iff (hc : S.Coord θ e) (p : PairMod (ZMod 2)) :
    S.vec e p ∈ I ↔ p ∈ V₁ (ZMod 2) := by
  rw [← hc.heI]
  constructor
  · intro h
    exact ⟨e.symm p, h, e.apply_symm_apply p⟩
  · rintro ⟨x, hx, hxp⟩
    have hx' : x = e.symm p := by
      rw [← hxp]
      exact (e.symm_apply_apply x).symm
    rw [hx'] at hx
    exact hx

theorem th_pow_three_mem (hc : S.Coord θ e) :
    θ ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have hθN := S.L_le_normalizer_V hc.mem
  have e3 : (⟨θ ^ 3, Subgroup.pow_mem _ hθN 3⟩ : Subgroup.normalizer (fsuV T I : Set G)) =
      ⟨θ, hθN⟩ ^ 3 := Subtype.ext (by simp)
  refine (convI_eq_one_iff S.hV ⟨θ ^ 3, Subgroup.pow_mem _ hθN 3⟩).mp ?_
  rw [e3, map_pow]
  exact congrHom_injective e (((map_pow (congrHom e) _ 3).trans
    ((congrArg (· ^ 3) hc.hθ).trans rho_th0_pow_three)).trans (map_one _).symm)

theorem th_not_mem (hc : S.Coord θ e) : θ ∉ Subgroup.centralizer (fsuV T I : Set G) := by
  intro h
  have h2 := hc.hθ
  rw [(convI_eq_one_iff S.hV ⟨θ, S.L_le_normalizer_V hc.mem⟩).mpr h, map_one] at h2
  exact th0_ne_one (SL3One.rho_injective (h2.symm.trans (map_one _).symm))

variable (S) in
theorem exists_coord' : ∃ θ e, S.Coord θ e := by
  obtain ⟨e₀, he₀, -⟩ := S.exists_model
  have h1 : SL3One.rho th0 ∈ (autI S.hV (fsuL0 T L)).map (congrHom e₀) := by
    rw [he₀]
    exact SL3One.rho_mem_pairSL th0
  obtain ⟨φ, hφ, hφe⟩ := h1
  obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := (mem_autI S.hV).1 hφ
  have hlL' : l ∈ L := by
    rw [S.hL]
    exact hlL
  have hl3 : l ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    have e3 : (⟨l ^ 3, Subgroup.pow_mem _ hlN 3⟩ : Subgroup.normalizer (fsuV T I : Set G)) =
        ⟨l, hlN⟩ ^ 3 := Subtype.ext (by simp)
    refine (convI_eq_one_iff S.hV ⟨l ^ 3, Subgroup.pow_mem _ hlN 3⟩).mp ?_
    rw [e3, map_pow]
    exact congrHom_injective e₀ (((map_pow (congrHom e₀) _ 3).trans
      ((congrArg (· ^ 3) hφe).trans rho_th0_pow_three)).trans (map_one _).symm)
  have hl1 : l ∉ Subgroup.centralizer (fsuV T I : Set G) := by
    intro h
    have h2 := hφe
    rw [(convI_eq_one_iff S.hV ⟨l, hlN⟩).mpr h, map_one] at h2
    exact th0_ne_one (SL3One.rho_injective (h2.symm.trans (map_one _).symm))
  obtain ⟨θ', e, hc, -⟩ := S.exists_coord hlL' hl3 hl1
  exact ⟨θ', e, hc⟩

theorem exists_swap (hc : S.Coord θ e) : ∃ t ∈ T, ∃ g : SL32,
    ∀ htN : t ∈ Subgroup.normalizer (fsuV T I : Set G),
      congrHom e (convI S.hV ⟨t, htN⟩) = swapAut (ZMod 2) * SL3One.rho g := by
  obtain ⟨t, htT, -, hinf, -⟩ := S.exists_twist
  have htN : t⁻¹ ∈ Subgroup.normalizer (fsuV T I : Set G) := S.T_le_normalizer_V (T.inv_mem htT)
  have hyN : congrHom e (convI S.hV ⟨t⁻¹, htN⟩) ∈ pairNorm (ZMod 2) := by
    rw [← S.map_autI_top_eq hc.he]
    exact ⟨_, convI_mem_autI S.hV (Subgroup.mem_top _) htN, rfl⟩
  obtain ⟨g, hg | hg⟩ := mem_pairNorm_iff.mp hyN
  · exfalso
    have h1 : congrHom e (convI S.hV ⟨t⁻¹, htN⟩) ∈
        (autI S.hV (fsuL0 T L)).map (congrHom e) := by
      rw [hc.he, hg]
      exact SL3One.rho_mem_pairSL g
    obtain ⟨y', hy', hyy'⟩ := h1
    rw [congrHom_injective e hyy'] at hy'
    obtain ⟨⟨l, hlN⟩, hlL, hle'⟩ := (mem_autI S.hV).1 hy'
    have hlL' : l ∈ L := by
      rw [S.hL]
      exact hlL
    apply S.I_ne.1
    rw [eq_bot_iff]
    intro v hv
    have hvV : v ∈ fsuV T I := le_fsuV I T hv
    have h1 := congrArg (fun φ : MulAut (IntMod (fsuV T I) S.hV) =>
      (φ (IntMod.mk S.hV ⟨v, hvV⟩)).val) hle'
    simp only [convI_apply_val] at h1
    have h2 : l * v * l⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp (S.L_le_normalizer_I hlL') v).mp hv
    have h3 : t⁻¹ * v * t ∈ I := by
      have h1' : l * v * l⁻¹ = t⁻¹ * v * t⁻¹⁻¹ := h1
      rw [h1', inv_inv] at h2
      exact h2
    have h5 : t⁻¹ * v * t ∈ CFSG.conjugate I t := by
      rw [mem_conjugate_iff']
      simpa [mul_assoc] using hv
    have h6 : t⁻¹ * v * t ∈ I ⊓ CFSG.conjugate I t := ⟨h3, h5⟩
    rw [hinf, Subgroup.mem_bot] at h6
    rw [Subgroup.mem_bot]
    calc v = t * (t⁻¹ * v * t) * t⁻¹ := by group
      _ = 1 := by rw [h6]; group
  · exact ⟨t⁻¹, T.inv_mem htT, g, fun _ => hg⟩

variable (S) in
theorem sylow_map_conj {t : G} (ht : t ∈ T) {W : Subgroup G}
    (hG : IsSylowTwoOf (T ⊓ Subgroup.centralizer (W : Set G)) (Subgroup.centralizer (W : Set G)))
    (hM : IsSylowTwoOf (T ⊓ Subgroup.centralizer (W : Set G))
      (fsuM T L ⊓ Subgroup.centralizer (W : Set G))) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ((W.map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G)) (Subgroup.centralizer ((W.map (MulAut.conj t).toMonoidHom : Subgroup G) :
        Set G)) ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((W.map (MulAut.conj t).toMonoidHom :
        Subgroup G) : Set G)) (fsuM T L ⊓ Subgroup.centralizer
        ((W.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)) := by
  have hT : T.map (MulAut.conj t).toMonoidHom = T :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer ht)
  have hMc : (fsuM T L).map (MulAut.conj t).toMonoidHom = fsuM T L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (S.T_le_fsuM ht))
  rw [CFSG.QuasithinUnique.centralizer_map_equiv]
  have hTC : T ⊓ (Subgroup.centralizer (W : Set G)).map (MulAut.conj t).toMonoidHom =
      (T ⊓ Subgroup.centralizer (W : Set G)).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hT]
  have hMC : fsuM T L ⊓ (Subgroup.centralizer (W : Set G)).map (MulAut.conj t).toMonoidHom =
      (fsuM T L ⊓ Subgroup.centralizer (W : Set G)).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj t).injective, hMc]
  rw [hTC, hMC]
  exact ⟨isSylowTwoOf_map_of_injective (MulAut.conj t).injective hG,
    isSylowTwoOf_map_of_injective (MulAut.conj t).injective hM⟩

theorem exists_conj_mem_I (h3104 : Stmt3_2_10_four) (hc : S.Coord θ e) {u : G} (hu : u ∈ I) :
    ∃ m ∈ fsuM T L, m * u * m⁻¹ ∈ I ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((Subgroup.zpowers (m * u * m⁻¹) : Subgroup G) :
        Set G)) (Subgroup.centralizer ((Subgroup.zpowers (m * u * m⁻¹) : Subgroup G) : Set G)) ∧
      IsSylowTwoOf (T ⊓ Subgroup.centralizer ((Subgroup.zpowers (m * u * m⁻¹) : Subgroup G) :
        Set G)) (fsuM T L ⊓ Subgroup.centralizer ((Subgroup.zpowers (m * u * m⁻¹) :
        Subgroup G) : Set G)) := by
  have huV : u ∈ fsuV T I := le_fsuV I T hu
  obtain ⟨m, hmM, hG, hM⟩ := S.exists_conj_sylow h3104 ((Subgroup.zpowers_le).mpr huV)
  rw [MonoidHom.map_zpowers] at hG hM
  obtain ⟨p, rfl⟩ := exists_vec (S := S) (e := e) huV
  have hp2 : (vp p).2 = 0 := mem_V₁_iff_vp.mp ((vec_mem_I_iff hc p).mp hu)
  have hmN := S.hMN hmM
  have hmu : m * S.vec e p * m⁻¹ = S.vec e (congrHom e (convI S.hV ⟨m, hmN⟩) p) :=
    conj_vec hmN p
  have hφN : congrHom e (convI S.hV ⟨m, hmN⟩) ∈ pairNorm (ZMod 2) := by
    rw [← S.map_autI_top_eq hc.he]
    exact ⟨_, convI_mem_autI S.hV (Subgroup.mem_top _) hmN, rfl⟩
  obtain ⟨g, hg | hg⟩ := mem_pairNorm_iff.mp hφN
  · refine ⟨m, hmM, ?_, hG, hM⟩
    rw [hmu, vec_mem_I_iff hc, hg, mem_V₁_iff_vp]
    change (vp (SL3One.rho g p)).2 = 0
    rw [vp_rho]
    change dact g (vp p).2 = 0
    rw [hp2]
    simp only [dact, Matrix.mulVec_zero]
  · obtain ⟨t, htT, g', hg'⟩ := S.exists_swap hc
    have htN := S.T_le_normalizer_V htT
    have hconj : t * m * S.vec e p * (t * m)⁻¹ = t * (m * S.vec e p * m⁻¹) * t⁻¹ := by group
    refine ⟨t * m, (fsuM T L).mul_mem (S.T_le_fsuM htT) hmM, ?_, ?_⟩
    · rw [hconj, hmu, conj_vec htN, hg' htN, vec_mem_I_iff hc, hg, mem_V₁_iff_vp]
      change (vp (swapAut (ZMod 2) (SL3One.rho g' (swapAut (ZMod 2)
        (SL3One.rho g p))))).2 = 0
      rw [vp_swap, vp_rho, vp_swap, vp_rho]
      change act g' (dact g (vp p).2) = 0
      rw [hp2]
      simp only [act, dact, Matrix.mulVec_zero]
    · have h := S.sylow_map_conj htT hG hM
      rw [MonoidHom.map_zpowers] at h
      rw [hconj]
      exact h

theorem exists_coord_a1 (hc : S.Coord θ e) {u : G} (hu : u ∈ I) (hu1 : u ≠ 1) :
    ∃ θ' e', S.Coord θ' e' ∧ S.vec e' a1 = u := by
  have huV : u ∈ fsuV T I := le_fsuV I T hu
  obtain ⟨p, rfl⟩ := exists_vec (S := S) (e := e) huV
  have hp2 : (vp p).2 = 0 := mem_V₁_iff_vp.mp ((vec_mem_I_iff hc p).mp hu)
  have ha : (vp p).1 ≠ 0 := by
    intro h
    apply hu1
    have : p = 1 := vp_injective (Prod.ext h hp2)
    rw [this, vec_one]
  obtain ⟨h, hh⟩ := trans_e1 _ ha
  have h1 : SL3One.rho h ∈ (autI S.hV (fsuL0 T L)).map (congrHom e) := by
    rw [hc.he]
    exact SL3One.rho_mem_pairSL h
  obtain ⟨φ, hφ, hφe⟩ := h1
  obtain ⟨⟨l, hlN⟩, hlL, rfl⟩ := (mem_autI S.hV).1 hφ
  have hlL' : l ∈ L := by
    rw [S.hL]
    exact hlL
  have hpa : SL3One.rho h a1 = p := by
    apply vp_injective
    rw [vp_rho]
    refine Prod.ext hh ?_
    change dact h 0 = (vp p).2
    rw [hp2]
    simp only [dact, Matrix.mulVec_zero]
  have hconj : S.vec e p = l * S.vec e a1 * l⁻¹ := by
    rw [conj_vec hlN, hφe]
    exact congrArg (S.vec e) hpa.symm
  have hθ₁L : l * θ * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hlL' hc.mem) (L.inv_mem hlL')
  have hθ₁3 : (l * θ * l⁻¹) ^ 3 ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [conj_pow]
    exact conj_mem_centralizer hlN (th_pow_three_mem hc)
  have hθ₁1 : l * θ * l⁻¹ ∉ Subgroup.centralizer (fsuV T I : Set G) := by
    intro h'
    apply th_not_mem hc
    have h2 := conj_mem_centralizer (Subgroup.inv_mem _ hlN) h'
    have e2 : l⁻¹ * (l * θ * l⁻¹) * l⁻¹⁻¹ = θ := by group
    rwa [e2] at h2
  have hu₁ : S.vec e p ∈ Subgroup.centralizer ({l * θ * l⁻¹} : Set G) := by
    rw [hconj, Subgroup.mem_centralizer_singleton_iff]
    have hz : S.vec e a1 ∈ Subgroup.centralizer ({θ} : Set G) := (vec_a1_mem_V0 hc).2
    rw [Subgroup.mem_centralizer_singleton_iff] at hz
    calc l * S.vec e a1 * l⁻¹ * (l * θ * l⁻¹) = l * (S.vec e a1 * θ) * l⁻¹ := by group
      _ = l * (θ * S.vec e a1) * l⁻¹ := by rw [hz]
      _ = l * θ * l⁻¹ * (l * S.vec e a1 * l⁻¹) := by group
  obtain ⟨θ', e', hc', hfix⟩ := S.exists_coord hθ₁L hθ₁3 hθ₁1
  refine ⟨θ', e', hc', ?_⟩
  have hu' := (hfix _ huV).mpr hu₁
  obtain ⟨q, hq⟩ := exists_vec (S := S) (e := e') huV
  have hq2 : (vp q).2 = 0 := mem_V₁_iff_vp.mp ((vec_mem_I_iff hc' q).mp (hq ▸ hu))
  have hqθ : SL3One.rho th0 q = q := by
    rw [← hq] at hu'
    have h3 := (vec_mem_centralizer_iff (S.L_le_normalizer_V hc'.mem) q).mp hu'
    rwa [hc'.hθ] at h3
  have hq1 : q ≠ 1 := by
    rintro rfl
    exact hu1 (hq.symm.trans vec_one)
  have hq0 : act th0 (vp q).1 = (vp q).1 :=
    (rho_fst th0 q).symm.trans (congrArg (fun r => Multiplicative.toAdd r.1) hqθ)
  rcases (fix_th0 _).mp hq0 with h0 | h0
  · exact absurd (vp_injective (Prod.ext h0 hq2 : vp q = vp 1)) hq1
  · rw [← hq]
    congr 1
    exact (vp_injective (Prod.ext h0 hq2 : vp q = vp a1)).symm

variable (S) in
theorem charTwo_of_mem_I (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight)
    (h443 : Stmt4_4_3Orbit') (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h755 : Input7_5_5)
    (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) (hA23 : A23FourCentralFact)
    (hmult : LieMultiplierFact) (hcart : LieCartanFact) (hthom : LieThompsonFact)
    (hr : (2 : ℕ∞) < rParam (fsuV T I)) {u : G} (hu : u ∈ I) (hu1 : u ≠ 1) :
    CharTwo (Subgroup.centralizer ({u} : Set G)) := by
  obtain ⟨θ₀', e₀', hc₀⟩ := S.exists_coord'
  obtain ⟨m, -, hmI, hG, hM⟩ := S.exists_conj_mem_I h3104 hc₀ hu
  rw [← charTwo_centralizer_conj m u]
  have hmu1 : m * u * m⁻¹ ≠ 1 := by
    intro h
    apply hu1
    calc u = m⁻¹ * (m * u * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  obtain ⟨θ, e, hc, hvec⟩ := S.exists_coord_a1 hc₀ hmI hmu1
  have hC : Subgroup.centralizer ((Subgroup.zpowers (m * u * m⁻¹) : Subgroup G) : Set G) =
      Subgroup.centralizer ({m * u * m⁻¹} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have C : S.Conf θ e (Subgroup.zpowers (m * u * m⁻¹))
      (Subgroup.centralizer ((Subgroup.zpowers (m * u * m⁻¹) : Subgroup G) : Set G)) :=
    ⟨hc, Or.inr ⟨by rw [hvec], hr⟩, hG, hM,
      sup_le ((oTwoUpper_le _).trans inf_le_right) inf_le_right, le_rfl⟩
  rw [← hC]
  exact C.charTwo h3108 h443 h37 h38 h37c h38c h755 kf1 h23 hA23 hmult hcart hthom

end Setup

theorem stmt7_7_2_of (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h711n : Stmt7_1_1_normal) (h325 : Stmt3_2_5)
    (h3104 : Stmt3_2_10_four) (h3108 : Stmt3_2_10_eight) (h443 : Stmt4_4_3Orbit')
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat) (h755 : Input7_5_5)
    (kf1 : OutTwoNilpotentFact) (h23 : A23SQTKListFact) (hA23 : A23FourCentralFact)
    (hmult : LieMultiplierFact) (hcart : LieCartanFact) (hthom : LieThompsonFact) :
    Stmt7_7_2 := by
  intro G _ _ T L I hyp h731 hcomm hrow hr x _ v hv hv1
  have S : Setup T L I := Setup.of h37 h38 h39 h3228 h711n h325 hyp h731 hrow
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hv
  have hu1 : u ≠ 1 := fun h => hv1 (by rw [h, map_one])
  change CharTwo (Subgroup.centralizer ({x⁻¹ * u * x⁻¹⁻¹} : Set G))
  rw [charTwo_centralizer_conj]
  exact S.charTwo_of_mem_I h3104 h3108 h443 h37 h38 h37c h38c h755 kf1 h23 hA23 hmult hcart hthom
    hr hu hu1

end CFSG.Quasithin.H13.Sec77
