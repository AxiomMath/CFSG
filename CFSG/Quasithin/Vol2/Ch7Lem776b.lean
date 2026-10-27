module

public import CFSG.Quasithin.Vol2.Ch7Sec77Vm
public import CFSG.Quasithin.Vol2.Ch7Lem755
public import CFSG.Quasithin.Background.HSL3S77Case
public import CFSG.Quasithin.Vol2.Ch7Lem775

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped IsMulCommutative Matrix

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem pv_add (x y : Vec × Vec) : pv (x + y) = pv x * pv y := rfl

theorem pv_smul_mem {P : Subgroup (PairMod (ZMod 2))} {x : Vec × Vec} (hx : pv x ∈ P)
    (c : ZMod 2) : pv (c • x) ∈ P := by
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
  · rw [zero_smul]
    exact P.one_mem
  · rwa [one_smul]

theorem h0_vec (p : PairMod (ZMod 2)) (c₁ c₂ ε₁ ε₂ : ZMod 2) :
    pv (c₁ • e1 + ε₁ • (vp p).1 + ε₂ • act th0 (vp p).1,
      c₂ • e1 + ε₁ • (vp p).2 + ε₂ • th0d *ᵥ (vp p).2) =
      pv (c₁ • ((e1, 0) : Vec × Vec)) * pv (c₂ • ((0, e1) : Vec × Vec)) * pv (ε₁ • vp p) *
        pv (ε₂ • vp (SL3One.rho th0 p)) := by
  rw [← pv_add, ← pv_add, ← pv_add, vp_rho, dact_th0]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst, smul_zero, add_zero]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]

theorem h1_vec (p : PairMod (ZMod 2)) (c ε₁ ε₂ : ZMod 2) :
    pv (c • e1 + ε₁ • (vp p).1 + ε₂ • act th0 (vp p).1, ε₁ • (vp p).2 + ε₂ • th0d *ᵥ (vp p).2) =
      pv (c • ((e1, 0) : Vec × Vec)) * pv (ε₁ • vp p) * pv (ε₂ • vp (SL3One.rho th0 p)) := by
  rw [← pv_add, ← pv_add, vp_rho, dact_th0]
  congr 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_fst]
  · simp only [Prod.snd_add, Prod.smul_snd, smul_zero, zero_add]

omit [Finite G] in
theorem conj_mem_centralizer {K : Subgroup G} {x w : G}
    (hx : x ∈ Subgroup.normalizer (K : Set G)) (hw : w ∈ Subgroup.centralizer (K : Set G)) :
    x * w * x⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hw ⊢
  intro k hk
  have hk' : x⁻¹ * k * x ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) k).mp hk
    simpa using this
  have h1 := hw _ hk'
  calc k * (x * w * x⁻¹) = x * ((x⁻¹ * k * x) * w) * x⁻¹ := by group
    _ = x * (w * (x⁻¹ * k * x)) * x⁻¹ := by rw [h1]
    _ = x * w * x⁻¹ * k := by group

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem fsuV_le_centralizer {Vp : Subgroup G} (hVpV : Vp ≤ fsuV T I) :
    fsuV T I ≤ Subgroup.centralizer (Vp : Set G) := fun v hv =>
  Subgroup.mem_centralizer_iff.mpr fun u hu =>
    congrArg Subtype.val (S.hV.1.is_comm.comm ⟨u, hVpV hu⟩ ⟨v, hv⟩)

theorem pCoreOf_ne_bot {Vp H : Subgroup G} (hVpV : Vp ≤ fsuV T I) {z : G} (hzVp : z ∈ Vp)
    (hz1 : z ≠ 1) (hTpH : T ⊓ Subgroup.centralizer (Vp : Set G) ≤ H)
    (hHG : H ≤ Subgroup.centralizer (Vp : Set G)) : pCoreOf 2 H ≠ ⊥ := by
  intro h
  have hVpH : Vp ≤ H := (le_inf (hVpV.trans S.fsuV_le_T)
    (hVpV.trans (S.fsuV_le_centralizer hVpV))).trans hTpH
  have hle : Vp ≤ pCoreOf 2 H := CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer hVpH
    (hHG.trans (Subgroup.centralizer_le_normalizer _)) (S.isPGroup_fsuV.to_le hVpV)
  rw [h] at hle
  exact hz1 (Subgroup.mem_bot.mp (hle hzVp))

theorem th_mem_oTwoUpper (hc : S.Coord θ e) {Vp : Subgroup G}
    (hVp : Vp ≤ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G)) :
    θ ∈ oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) := by
  refine mem_oTwoUpper_of_odd ⟨hc.mem, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩ hc.odd
  exact Subgroup.mem_centralizer_singleton_iff.mp (hVp hv).2

theorem oddCoreIn_eq_bot_of_coord (hc : S.Coord θ e) {Vp H : Subgroup G}
    (hVp : Vp ≤ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G)) {z : G} (hzVp : z ∈ Vp)
    (hz1 : z ≠ 1)
    (hA : Subgroup.centralizer (Vp : Set G) ⊓ Subgroup.centralizer (S.vm e : Set G) ≤ fsuM T L)
    (hLH : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
      (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H)
    (hHG : H ≤ Subgroup.centralizer (Vp : Set G)) : oddCoreIn H = ⊥ := by
  have hVpV : Vp ≤ fsuV T I := hVp.trans inf_le_left
  have hTpH : T ⊓ Subgroup.centralizer (Vp : Set G) ≤ H := le_sup_right.trans hLH
  have hVTp : fsuV T I ≤ T ⊓ Subgroup.centralizer (Vp : Set G) :=
    le_inf S.fsuV_le_T (S.fsuV_le_centralizer hVpV)
  have hQH : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ H :=
    (inf_le_inf_left _ (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hVpV))).trans hTpH
  have hθH : θ ∈ H := le_sup_left.trans hLH (S.th_mem_oTwoUpper hc hVp)
  refine S.oddCoreIn_eq_bot hQH (S.pCoreOf_ne_bot hVpV hzVp hz1 hTpH hHG) hHG vm_le
    ((vm_le (S := S)).trans (hVTp.trans hTpH)) ((Subgroup.zpowers_le).mpr hθH) ?_
    (commutator_vm hc) hA
  rw [Nat.card_zpowers]
  exact hc.odd

theorem th_mem_normalizer (hc : S.Coord θ e) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) {Vp H K : Subgroup G}
    (hVp : Vp ≤ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G)) {z : G} (hzVp : z ∈ Vp)
    (hz1 : z ≠ 1)
    (hLH : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
      (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H)
    (hHG : H ≤ Subgroup.centralizer (Vp : Set G)) (hK : IsComponentIn K H) :
    θ ∈ Subgroup.normalizer (K : Set G) := by
  have hVpV : Vp ≤ fsuV T I := hVp.trans inf_le_left
  have hθH : θ ∈ H := le_sup_left.trans hLH (S.th_mem_oTwoUpper hc hVp)
  exact S.oTwoUpper_le_normalizer h37c h38c
    (S.pCoreOf_ne_bot hVpV hzVp hz1 (le_sup_right.trans hLH) hHG) hK
    (mem_oTwoUpper_of_odd hθH hc.odd)

theorem false_of_singDiag (h3108 : Stmt3_2_10_eight) (hc : S.Coord θ e) {Vp H K : Subgroup G}
    (hVpV : Vp ≤ fsuV T I) (hzVp : S.vec e a1 ∈ Vp)
    (hTp : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G))
      (fsuM T L ⊓ Subgroup.centralizer (Vp : Set G)))
    (hLH : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ⊔
      (T ⊓ Subgroup.centralizer (Vp : Set G)) ≤ H)
    (hHG : H ≤ Subgroup.centralizer (Vp : Set G)) (hK : IsComponentIn K H)
    {s : PairMod (ZMod 2)} (hs : s ∈ sdSet)
    (hsK : S.vec e s ∈ Subgroup.centralizer (K : Set G)) : False := by
  obtain ⟨S₀, hS₀, huS₀, huZ⟩ := S.exists_sylow_of_singDiag hc.he (vec_mem (S := S) (e := e) s)
    (by rw [e_vec]; exact hs)
  have hu1 : S.vec e s ≠ 1 := by
    intro h
    have h2 : s = 1 := vec_injective (h.trans vec_one.symm)
    rw [h2] at hs
    exact hs.1 rfl
  have hCT := S.charTwo_inf_centralizer h3108 (le_fsuV I T) S.L_le_normalizer_I S.I_ne.1
    S.I_ne.2 hVpV (vec_a1_mem hc) vec_a1_ne_one hzVp hTp hLH hHG (vec_mem s) hu1 hS₀ huS₀ huZ
  have hKu : K ≤ Subgroup.centralizer ({S.vec e s} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hsK k hk)
  exact DoubleA3.not_isComponentIn_of_charTwo hCT K
    (BenderBranch.isComponentIn_of_le hK (le_inf hK.1 hKu) inf_le_left)

theorem not_mem_centralizer_H0 (h3108 : Stmt3_2_10_eight) (hc : S.Coord θ e) {H K : Subgroup G}
    (hTp : IsSylowTwoOf (T ⊓ Subgroup.centralizer
      ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G))
      (fsuM T L ⊓ Subgroup.centralizer
        ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G)))
    (hLH : oTwoUpper (L ⊓ Subgroup.centralizer
      ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G)) ⊔
      (T ⊓ Subgroup.centralizer
        ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G)) ≤ H)
    (hHG : H ≤ Subgroup.centralizer
      ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G))
    (hK : IsComponentIn K H) (hθK : θ ∈ Subgroup.normalizer (K : Set G)) {w : G}
    (hw : w ∈ S.vm e) (hw1 : w ≠ 1) : w ∉ Subgroup.centralizer (K : Set G) := by
  intro hwK
  set P := (Subgroup.centralizer (K : Set G)).comap
    ((E3.valHom S.hV).comp e.symm.toMonoidHom) with hP
  have hmemP : ∀ p, p ∈ P ↔ S.vec e p ∈ Subgroup.centralizer (K : Set G) := fun _ => Iff.rfl
  have hV0K : ∀ v ∈ fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G),
      v ∈ Subgroup.centralizer (K : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      (Subgroup.mem_centralizer_iff.mp (hHG (hK.1 hk)) v hv).symm
  obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hw
  have hpP : p ∈ P := (hmemP p).mpr hwK
  have hqP : SL3One.rho th0 p ∈ P := by
    rw [hmemP, ← conj_vec_th hc]
    exact conj_mem_centralizer hθK hwK
  have haP : a1 ∈ P := (hmemP a1).mpr (hV0K _ (vec_a1_mem_V0 hc))
  have hbP : b1 ∈ P := (hmemP b1).mpr (hV0K _ (vec_b1_mem_V0 hc))
  have hne : vp p ≠ 0 := fun h => hw1 (by
    rw [show p = 1 from vp_injective (show vp p = vp 1 from h), vec_one])
  obtain ⟨c₁, c₂, ε₁, ε₂, hsd⟩ := h0_case (vp p) ⟨hp, hne⟩
  have hsP : pv (c₁ • e1 + ε₁ • (vp p).1 + ε₂ • act th0 (vp p).1,
      c₂ • e1 + ε₁ • (vp p).2 + ε₂ • th0d *ᵥ (vp p).2) ∈ P := by
    rw [h0_vec]
    exact P.mul_mem (P.mul_mem (P.mul_mem (pv_smul_mem (x := ((e1, 0) : Vec × Vec)) haP c₁)
      (pv_smul_mem (x := ((0, e1) : Vec × Vec)) hbP c₂)) (pv_smul_mem (x := vp p) hpP ε₁))
      (pv_smul_mem (x := vp (SL3One.rho th0 p)) hqP ε₂)
  exact S.false_of_singDiag h3108 hc inf_le_left (vec_a1_mem_V0 hc) hTp hLH hHG hK hsd hsP

theorem mem_centralizer_of_fix (hc : S.Coord θ e) {p : PairMod (ZMod 2)}
    (hfix : ∀ g : SL32, (act g e1 = e1 ∧ act g (vp p).1 = (vp p).1 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ (vp p).2 = (vp p).2 ∧
      act g (act th0 (vp p).1) = act th0 (vp p).1 ∧
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ (th0d *ᵥ (vp p).2) = th0d *ᵥ (vp p).2) → g = 1)
    {g : G} (hgM : g ∈ fsuM T L) (ha : g ∈ Subgroup.centralizer ({S.vec e a1} : Set G))
    (hp : g ∈ Subgroup.centralizer ({S.vec e p} : Set G))
    (hq : g ∈ Subgroup.centralizer ({S.vec e (SL3One.rho th0 p)} : Set G)) :
    g ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  have hgN := S.hMN hgM
  have hφN : congrHom e (convI S.hV ⟨g, hgN⟩) ∈ pairNorm (ZMod 2) := by
    rw [← S.map_autI_top_eq hc.he]
    exact ⟨_, convI_mem_autI S.hV (Subgroup.mem_top g) hgN, rfl⟩
  have ha' := (mem_centralizer_vec_iff hgN a1).mp ha
  have hp' := (mem_centralizer_vec_iff hgN p).mp hp
  have hq' := (mem_centralizer_vec_iff hgN _).mp hq
  obtain ⟨g', hg' | hg'⟩ := mem_pairNorm_iff.mp hφN
  · rw [hg'] at ha' hp' hq'
    have hfix' : ∀ x : PairMod (ZMod 2), SL3One.rho g' x = x →
        act g' (vp x).1 = (vp x).1 ∧
          (g' : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ (vp x).2 = (vp x).2 := by
      intro x hx
      have h1 := congrArg vp hx
      rw [vp_rho] at h1
      exact ⟨congrArg Prod.fst h1, (dact_eq_iff g' _).mp (congrArg Prod.snd h1)⟩
    obtain ⟨ha1, -⟩ := hfix' a1 ha'
    obtain ⟨hp1, hp2⟩ := hfix' p hp'
    obtain ⟨hq1, hq2⟩ := hfix' _ hq'
    rw [vp_rho, dact_th0] at hq1 hq2
    have hg1 : g' = 1 := hfix g' ⟨ha1, hp1, hp2, hq1, hq2⟩
    rw [hg1, map_one] at hg'
    exact (convI_eq_one_iff S.hV _).mp ((congrHom_injective e) (hg'.trans (map_one _).symm))
  · exfalso
    rw [hg'] at ha'
    have h1 := congrArg (fun x => (vp x).1) ha'
    change Multiplicative.toAdd (SL3One.rho g' a1).2 = e1 at h1
    rw [rho_snd] at h1
    change dact g' 0 = e1 at h1
    rw [dact, Matrix.mulVec_zero] at h1
    exact absurd (congrFun h1 0) (by decide)

theorem not_mem_centralizer_H1 (h3108 : Stmt3_2_10_eight) (h755 : Input7_5_5)
    (hr : (2 : ℕ∞) < rParam (fsuV T I)) (hc : S.Coord θ e) {H K : Subgroup G}
    (hTp : IsSylowTwoOf (T ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (S.vec e a1) : Subgroup G) : Set G))
      (fsuM T L ⊓ Subgroup.centralizer ((Subgroup.zpowers (S.vec e a1) : Subgroup G) : Set G)))
    (hLH : oTwoUpper (L ⊓ Subgroup.centralizer
      ((Subgroup.zpowers (S.vec e a1) : Subgroup G) : Set G)) ⊔
      (T ⊓ Subgroup.centralizer ((Subgroup.zpowers (S.vec e a1) : Subgroup G) : Set G)) ≤ H)
    (hHG : H ≤ Subgroup.centralizer ((Subgroup.zpowers (S.vec e a1) : Subgroup G) : Set G))
    (hK : IsComponentIn K H) (hKM : ¬ K ≤ fsuM T L)
    (hθK : θ ∈ Subgroup.normalizer (K : Set G)) {w : G} (hw : w ∈ S.vm e) (hw1 : w ≠ 1) :
    w ∉ Subgroup.centralizer (K : Set G) := by
  intro hwK
  set P := (Subgroup.centralizer (K : Set G)).comap
    ((E3.valHom S.hV).comp e.symm.toMonoidHom) with hP
  have hmemP : ∀ p, p ∈ P ↔ S.vec e p ∈ Subgroup.centralizer (K : Set G) := fun _ => Iff.rfl
  have haK : S.vec e a1 ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk =>
      (Subgroup.mem_centralizer_iff.mp (hHG (hK.1 hk)) _ (Subgroup.mem_zpowers _)).symm
  obtain ⟨p, hp, rfl⟩ := mem_vm_iff.mp hw
  have hqK : S.vec e (SL3One.rho th0 p) ∈ Subgroup.centralizer (K : Set G) := by
    rw [← conj_vec_th hc]
    exact conj_mem_centralizer hθK hwK
  have hne : vp p ≠ 0 := fun h => hw1 (by
    rw [show p = 1 from vp_injective (show vp p = vp 1 from h), vec_one])
  rcases h1_case (vp p) ⟨hp, hne⟩ with ⟨c, ε₁, ε₂, hsd⟩ | hfix
  · have hsP : pv (c • e1 + ε₁ • (vp p).1 + ε₂ • act th0 (vp p).1,
        ε₁ • (vp p).2 + ε₂ • th0d *ᵥ (vp p).2) ∈ P := by
      rw [h1_vec]
      exact P.mul_mem (P.mul_mem (pv_smul_mem (x := ((e1, 0) : Vec × Vec)) ((hmemP a1).mpr haK) c)
        (pv_smul_mem (x := vp p) ((hmemP p).mpr hwK) ε₁))
        (pv_smul_mem (x := vp (SL3One.rho th0 p)) ((hmemP _).mpr hqK) ε₂)
    exact S.false_of_singDiag h3108 hc ((Subgroup.zpowers_le).mpr (vec_mem a1))
      (Subgroup.mem_zpowers _) hTp hLH hHG hK hsd hsP
  ·
    set U₀ := fsuV T I ⊓ Subgroup.centralizer (K : Set G) with hU₀
    have hfixU : ∀ x ∈ U₀, ∀ g ∈ Subgroup.centralizer (U₀ : Set G),
        g ∈ Subgroup.centralizer ({x} : Set G) := fun x hx g hg =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hg x hx).symm
    have hCM : fsuM T L ⊓ Subgroup.centralizer (U₀ : Set G) ≤
        Subgroup.centralizer (fsuV T I : Set G) := fun g hg =>
      S.mem_centralizer_of_fix hc hfix hg.1 (hfixU _ ⟨vec_mem a1, haK⟩ g hg.2)
        (hfixU _ ⟨vec_mem p, hwK⟩ g hg.2) (hfixU _ ⟨vec_mem _, hqK⟩ g hg.2)
    have hCU₀ : ¬ Subgroup.centralizer (U₀ : Set G) ≤ fsuM T L := fun h =>
      hKM fun k hk => h (Subgroup.mem_centralizer_iff.mpr fun u hu =>
        (Subgroup.mem_centralizer_iff.mp hu.2 k hk).symm)
    obtain ⟨U₂, hU₀U₂, hU₂V, hCU₂, hmax⟩ := exists_maximal_centralizer inf_le_left hCU₀
    have hU₂1 : U₂ ≠ ⊥ := fun h =>
      vec_a1_ne_one (S := S) (Subgroup.mem_bot.mp (h ▸ hU₀U₂ ⟨vec_mem a1, haK⟩))
    have hCM₂ : fsuM T L ⊓ Subgroup.centralizer (U₂ : Set G) ≤
        Subgroup.centralizer (fsuV T I : Set G) := fun g hg =>
      hCM ⟨hg.1, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hU₀U₂) hg.2⟩
    have hres : twoPrimeResidual (fsuM T L ⊓ Subgroup.centralizer (U₂ : Set G)) ≤
        fsuM T L ⊓ Subgroup.centralizer (U₂ : Set G) :=
      iInf₂_le _ ⟨le_rfl, Subgroup.le_normalizer, by rw [Subgroup.relIndex_self]; norm_num⟩
    have hΓ : U₂ ∈ E6.gammaE64 (fsuV T I) (fsuM T L) :=
      ⟨hU₂V, hU₂1, hCU₂, hres.trans (le_inf inf_le_left hCM₂)⟩
    have hm : 2 < mQuot (fsuV T I) U₂ := by
      have h1 : rParam (fsuV T I) ≤ (mQuot (fsuV T I) U₂ : ℕ∞) := by
        unfold rParam
        exact iInf₂_le U₂ ⟨hU₂V, fun h => hCU₂ (h.trans S.hNM)⟩
      exact_mod_cast hr.trans_le h1
    obtain ⟨y, hy, hyo⟩ := h755 G T L I S.hyp S.hV U₂ hΓ hmax (by omega)
    have hbot : autI S.hV (fsuM T L ⊓ Subgroup.centralizer (U₂ : Set G)) = ⊥ :=
      (autI_eq_bot_iff S.hV (inf_le_left.trans S.hMN)).mpr hCM₂
    rw [hbot, Subgroup.mem_bot] at hy
    rw [hy, orderOf_one] at hyo
    have h8 : 2 ^ 3 ≤ 2 ^ mQuot (fsuV T I) U₂ := Nat.pow_le_pow_right (by norm_num) hm
    omega

end Setup

end CFSG.Quasithin.H13.Sec77
