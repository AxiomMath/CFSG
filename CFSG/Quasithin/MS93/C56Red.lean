module

public import CFSG.Quasithin.MS93.C56Stmt
public import CFSG.Quasithin.MS93.S5B512OneStmt
public import CFSG.Quasithin.MS93.S5A56
public import CFSG.Quasithin.MS93.S5BEqv

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5C56

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem exists_isPGroup_vIm_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {Y : Subgroup ↥(StatedSp 2 F)} (hY : IsPGroup 2 Y) :
    ∃ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a Y ∧ IsPGroup 2 E ∧
      S5.vIm h.le a E = Y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C : Subgroup ↥M := Y.comap a with hC
  let f : ↥C →* ↥Y := (a.comp C.subtype).codRestrict Y (fun x => x.2)
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := hd.2.2.1 y
    exact ⟨⟨m, hy⟩, rfl⟩
  have hYtop : IsPGroup 2 (⊤ : Subgroup ↥Y) := fun x => by
    obtain ⟨n, hn⟩ := hY x.1
    exact ⟨n, Subtype.ext hn⟩
  let S : Sylow 2 ↥Y := hYtop.toSylow (by rw [Subgroup.index_top]; norm_num)
  obtain ⟨P, hP⟩ := Sylow.mapSurjective_surjective hf 2 S
  have hPmap : (P : Subgroup ↥C).map f = ⊤ := by
    have := congrArg (fun Q : Sylow 2 ↥Y => (Q : Subgroup ↥Y)) hP
    simpa [S] using this
  refine ⟨((P : Subgroup ↥C).map C.subtype).map (puAmalgam h.le).ofA, ?_, ?_, ?_⟩
  · rintro _ ⟨m, ⟨c, -, rfl⟩, rfl⟩
    exact ⟨c, c.2, rfl⟩
  · exact (P.2.map C.subtype).map _
  · ext y
    constructor
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨m', ⟨c, -, rfl⟩, he⟩ := hm
      rw [← (puAmalgam h.le).ofA_injective he]
      exact c.2
    · intro hy
      have hmem : (⟨y, hy⟩ : ↥Y) ∈ (P : Subgroup ↥C).map f := hPmap ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hce⟩ := hmem
      exact ⟨c, ⟨c, ⟨c, hc, rfl⟩, rfl⟩, congrArg Subtype.val hce⟩

omit [Finite G] in
theorem isPGroup_qLine (hd : S5.IsSp4Data M T L k F a) {l : Submodule F (MSP.V4 F)}
    (hl : MSP.IsLine l) : IsPGroup 2 (MSP.qLine l) ∧ Nat.card (MSP.qLine l) = (2 ^ k) ^ 3 := by
  have hcard : Nat.card (MSP.qLine l) = (2 ^ k) ^ 3 := by
    rw [MSP.card_qLine hl, Nat.card_eq_fintype_card, hd.2.1]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨IsPGroup.of_card (n := 3 * k) ?_, hcard⟩
  rw [hcard, ← pow_mul, mul_comm]

theorem mem_stabCenter_of_forall {A B C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {δ : Vtx X} {z : X.Universal} (hz : z ∈ stab X δ)
    (hc : ∀ y ∈ stab X δ, y * z = z * y) : z ∈ stabCenter X δ :=
  ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun y => Subtype.ext (hc y y.2), rfl⟩

theorem mul_comm_of_mem_stabCenter {A B C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {δ : Vtx X} {z y : X.Universal} (hz : z ∈ stabCenter X δ)
    (hy : y ∈ stab X δ) : y * z = z * y := by
  obtain ⟨w, hw, rfl⟩ := hz
  exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hw ⟨y, hy⟩)

theorem le_stabCenter_of_gen (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l) {g : (puAmalgam h.le).Universal}
    (hgen : ∀ E : Subgroup (puAmalgam h.le).Universal, E ≤ S5.vPre h.le a (MSP.qLine l) →
      IsPGroup 2 E → (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E →
      S5.rconj g E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _)) :
    ZM _ (baseA (puAmalgam h.le)) ⊓
        Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (S5.rconj g (S5.vPre h.le a (MSP.qLine l)) :
          Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  obtain ⟨hl2, hlc⟩ := isPGroup_qLine hd hl
  obtain ⟨E, hEle, hE2, hEim⟩ := exists_isPGroup_vIm_eq h hd hl2
  have hEst : E ≤ stab _ (baseA (puAmalgam h.le)) := hEle.trans (S5.vPre_le_stab h _)
  have hErel : (Qv _ (baseA (puAmalgam h.le))).relIndex E = (2 ^ k) ^ 3 := by
    rw [← S5.card_vIm h hd hEst hE2, hEim, hlc]
  have hk : 1 ≤ k := hd.1
  have hlt : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
    rw [hErel]
    exact Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)
  have hst := hgen E hEle hE2 hlt
  rintro z ⟨⟨hzZ, hzC⟩, hzCg⟩
  have hzst : z ∈ stab _ (baseA (puAmalgam h.le)) :=
    (zm_le_qv_self _ hα hb0).trans (qv_le_stab _ _) hzZ
  refine mem_stabCenter_of_forall hzst fun y hy => ?_
  rw [← hst] at hy
  have hle : S5.rconj g E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) ≤
      Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hzCg e ((S5B.rconj_le_rconj_iff (g := g)).2 hEle he)
    · intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hzC e (hEle he)
    · intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα hzZ) e he
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

omit [Finite G] [Fintype F] in
theorem vPre_le_normalizer_vPre (hTM : T ≤ M) {Y Y' : Subgroup ↥(StatedSp 2 F)}
    (hY : Y' ≤ Subgroup.normalizer (Y : Set ↥(StatedSp 2 F))) :
    S5.vPre hTM a Y' ≤
      Subgroup.normalizer (S5.vPre hTM a Y : Set (puAmalgam hTM).Universal) := by
  refine le_normalizer_of_map_conj_le fun y hy => ?_
  obtain ⟨m, hm, rfl⟩ := hy
  rintro _ ⟨_, ⟨n, hn, rfl⟩, rfl⟩
  refine ⟨m * n * m⁻¹, ?_, ?_⟩
  · change a (m * n * m⁻¹) ∈ Y
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hY hm) (a n)).1 hn
  · simp [map_mul, map_inv]

theorem relIndex_rconj (h : PUHyp M T L) {y : (puAmalgam h.le).Universal}
    (hy : y ∈ stab _ (baseA (puAmalgam h.le))) (E : Subgroup (puAmalgam h.le).Universal) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex (S5.rconj y E) =
      (Qv _ (baseA (puAmalgam h.le))).relIndex E := by
  have hQ : (Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj y⁻¹).toMonoidHom =
      Qv _ (baseA (puAmalgam h.le)) := by
    rw [← qv_smul, (mem_stab _).1 (inv_mem hy)]
  calc (Qv _ (baseA (puAmalgam h.le))).relIndex (S5.rconj y E) =
        ((Qv _ (baseA (puAmalgam h.le))).map (MulAut.conj y⁻¹).toMonoidHom).relIndex
          (E.map (MulAut.conj y⁻¹).toMonoidHom) := by rw [S5B.rconj_eq_map, hQ]
    _ = (Qv _ (baseA (puAmalgam h.le))).relIndex E :=
      Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective

theorem zm_inf_zm_smul_le (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)}
    {K : Subgroup (puAmalgam h.le).Universal}
    (hZ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      Subgroup.centralizer (K : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le))) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (y • γ) ≤
      Subgroup.centralizer (S5.rconj y⁻¹ K : Set (puAmalgam h.le).Universal) := by
  have h1 := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) hZ
  rw [Subgroup.map_inf _ _ _ (MulAut.conj y).injective, ← zm_smul, ← zm_smul, (mem_stab _).1 hy,
    ← PU.centralizer_map_mulEquiv] at h1
  rw [S5B.rconj_eq_map, inv_inv]
  exact h1

theorem c56g_at (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hZ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hconc : S5.Concl56 h (2 ^ k) a α' l g x) :
    ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
        ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  intro z hz
  have h1 := hZ ⟨hz.1.2, hz.2⟩
  have h2 := zm_inf_zm_smul_le h hZ (inv_mem hg) ⟨hz.1.2, hz.1.1⟩
  rw [inv_inv] at h2
  refine le_stabCenter_of_gen h hd hl (g := g) (fun E hE hE2 hErel => ?_) ⟨⟨hz.1.2, h1⟩, h2⟩
  refine hconc.1 (S5.rconj g E) E (hE2.map _) hE2 ((S5B.rconj_le_rconj_iff (g := g)).2 hE) hE
    ?_ hErel
  rw [relIndex_rconj h hg]
  exact hErel

theorem c56x_at (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hZ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hconc : S5.Concl56 h (2 ^ k) a α' l g x)
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k) :
    ZM _ (x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
        ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le)) := by
  obtain ⟨ha, -, -, hdq⟩ := hconc
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hxP := hdq hidx
  have hN : S5.vPre h.le a (MSP.stab l) ≤ Subgroup.normalizer
      (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) :=
    vPre_le_normalizer_vPre h.le (MSP.stab_le_normalizer_fixer l)
  have hrx : S5.rconj x⁻¹ (S5.vPre h.le a (MSP.qLine l)) = S5.vPre h.le a (MSP.qLine l) := by
    rw [S5B.rconj_eq_map, inv_inv]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hN hxP)
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  intro z hz
  have h1 := hZ ⟨hz.1.2, hz.2⟩
  have hzμ : z ∈ ZM _ ((g * x)⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) := by
    rw [mul_inv_rev, mul_smul]
    exact hz.1.1
  have h2 := zm_inf_zm_smul_le h hZ (inv_mem hgx) ⟨hz.1.2, hzμ⟩
  rw [inv_inv] at h2
  refine le_stabCenter_of_gen h hd hl (g := g * x) (fun E hE hE2 hErel => ?_) ⟨⟨hz.1.2, h1⟩, h2⟩
  have hE' : S5.rconj x⁻¹ E ≤ S5.vPre h.le a (MSP.qLine l) := by
    rw [← hrx]
    exact (S5B.rconj_le_rconj_iff (g := x⁻¹)).2 hE
  have h0 := ha (S5.rconj g E) (S5.rconj x⁻¹ E) (hE2.map _) (hE2.map _)
    ((S5B.rconj_le_rconj_iff (g := g)).2 hE) hE'
    (by rw [relIndex_rconj h hg]; exact hErel)
    (by rw [relIndex_rconj h (inv_mem hxst)]; exact hErel)
  have h3 := congrArg (S5.rconj x) h0
  rw [S5B.rconj_sup, S5B.rconj_sup, ← S5B.rconj_mul, S5B.rconj_rconj_inv,
    S5B.rconj_eq_self_of_mem hxst] at h3
  have hQx : S5.rconj x (Qv _ (baseA (puAmalgam h.le))) = Qv _ (baseA (puAmalgam h.le)) := by
    rw [S5B.rconj_eq_map, ← qv_smul, (mem_stab _).1 (inv_mem hxst)]
  rw [hQx] at h3
  exact h3

theorem c56x_of (hzz : S5B.ZZ56) : C56x := by
  intro G _ _ M T L h hmin hb4 k F _ _ a hd α' hc hαβ l hl g hg x hx hconc
  have hZ := hzz G M T L h hmin hb4 k F _ _ a hd α' hc hαβ l hl
  exact ⟨c56g_at h hd hl.2.1 hZ hg hconc, fun hidx => c56x_at h hd hl.2.1 hZ hg hx hconc hidx⟩

theorem c56g_of (hzz : S5B.ZZ56) : C56g := c56g_of_c56x (c56x_of hzz)

theorem zm_inf_le_stabCenter_of_mem_lam (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)}
    (hZ : ∀ l : Submodule F (MSP.V4 F),
      S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
      ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
        Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal))
    (hl : ∃ l, S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l)
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k)
    {μ : Vtx (puAmalgam h.le)}
    (hμ : μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2)) :
    ZM _ μ ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  obtain ⟨g, x, hg, hx, hcase, hμe⟩ := hμ
  rcases hcase with ⟨hno, -⟩ | ⟨l', hl', hconc⟩
  · obtain ⟨l, hl⟩ := hl
    exact absurd hl (hno l)
  · rcases hμe with rfl | rfl
    · exact c56g_at h hd hl'.2.1 (hZ l' hl') hg hconc
    · exact c56x_at h hd hl'.2.1 (hZ l' hl') hg hx hconc hidx


omit [Fintype F] in
theorem le_stabCenter_of_sup_eq (h : PUHyp M T L) {g : (puAmalgam h.le).Universal}
    {E : Subgroup (puAmalgam h.le).Universal}
    (hst : S5.rconj g E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) = stab _ (baseA _)) :
    ZM _ (baseA (puAmalgam h.le)) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) ⊓
        Subgroup.centralizer (S5.rconj g E : Set (puAmalgam h.le).Universal) ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  rintro z ⟨⟨hzZ, hzC⟩, hzCg⟩
  have hzst : z ∈ stab _ (baseA (puAmalgam h.le)) :=
    (zm_le_qv_self _ hα hb0).trans (qv_le_stab _ _) hzZ
  refine mem_stabCenter_of_forall hzst fun y hy => ?_
  rw [← hst] at hy
  have hle : S5.rconj g E ⊔ E ⊔ Qv _ (baseA (puAmalgam h.le)) ≤
      Subgroup.centralizer ({z} : Set (puAmalgam h.le).Universal) := by
    refine sup_le (sup_le ?_ ?_) ?_
    · intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hzCg e he
    · intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 hzC e he
    · intro e he
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hα hzZ) e he
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hy)

omit [Fintype F] in
theorem c56g_two_of_le (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ S5.vPre h.le a (MSP.qLine l)) (hE2 : IsPGroup 2 E)
    (hErel : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E)
    {γ δ : Vtx (puAmalgam h.le)}
    (hZγ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    (hZδ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hconc : S5.Concl56 h (2 ^ k) a α' l g x) :
    ZM _ (g⁻¹ • δ) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  have hst := hconc.1 (S5.rconj g E) E (hE2.map _) hE2 ((S5B.rconj_le_rconj_iff (g := g)).2 hE)
    hE (by rw [relIndex_rconj h hg]; exact hErel) hErel
  intro z hz
  have h1 := hZγ ⟨hz.1.2, hz.2⟩
  have h2 := zm_inf_zm_smul_le h hZδ (inv_mem hg) ⟨hz.1.2, hz.1.1⟩
  rw [inv_inv] at h2
  exact le_stabCenter_of_sup_eq h hst ⟨⟨hz.1.2, h1⟩, h2⟩

omit [Fintype F] in
theorem c56x_two_of_le (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ S5.vPre h.le a (MSP.qLine l)) (hE2 : IsPGroup 2 E)
    (hErel : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E)
    {γ δ : Vtx (puAmalgam h.le)}
    (hZγ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    (hZδ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ δ ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hconc : S5.Concl56 h (2 ^ k) a α' l g x)
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k) :
    ZM _ (x⁻¹ • g⁻¹ • δ) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ γ ≤
      stabCenter _ (baseA (puAmalgam h.le)) := by
  obtain ⟨ha, -, -, hdq⟩ := hconc
  have hxst : x ∈ stab _ (baseA (puAmalgam h.le)) := puTrans_le_stab h.le L _ hx
  have hN : S5.vPre h.le a (MSP.stab l) ≤ Subgroup.normalizer
      (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal) :=
    vPre_le_normalizer_vPre h.le (MSP.stab_le_normalizer_fixer l)
  have hrx : S5.rconj x⁻¹ (S5.vPre h.le a (MSP.qLine l)) = S5.vPre h.le a (MSP.qLine l) := by
    rw [S5B.rconj_eq_map, inv_inv]
    exact (Subgroup.mem_normalizer_iff_map_conj_eq).1 (hN (hdq hidx))
  have hgx : g * x ∈ stab _ (baseA (puAmalgam h.le)) := mul_mem hg hxst
  have hE' : S5.rconj x⁻¹ E ≤ S5.vPre h.le a (MSP.qLine l) := by
    rw [← hrx]
    exact (S5B.rconj_le_rconj_iff (g := x⁻¹)).2 hE
  have h0 := ha (S5.rconj g E) (S5.rconj x⁻¹ E) (hE2.map _) (hE2.map _)
    ((S5B.rconj_le_rconj_iff (g := g)).2 hE) hE'
    (by rw [relIndex_rconj h hg]; exact hErel)
    (by rw [relIndex_rconj h (inv_mem hxst)]; exact hErel)
  have h3 := congrArg (S5.rconj x) h0
  rw [S5B.rconj_sup, S5B.rconj_sup, ← S5B.rconj_mul, S5B.rconj_rconj_inv,
    S5B.rconj_eq_self_of_mem hxst] at h3
  have hQx : S5.rconj x (Qv _ (baseA (puAmalgam h.le))) = Qv _ (baseA (puAmalgam h.le)) := by
    rw [S5B.rconj_eq_map, ← qv_smul, (mem_stab _).1 (inv_mem hxst)]
  rw [hQx] at h3
  intro z hz
  have h1 := hZγ ⟨hz.1.2, hz.2⟩
  have hzμ : z ∈ ZM _ ((g * x)⁻¹ • δ) := by
    rw [mul_inv_rev, mul_smul]
    exact hz.1.1
  have h2 := zm_inf_zm_smul_le h hZδ (inv_mem hgx) ⟨hz.1.2, hzμ⟩
  rw [inv_inv] at h2
  exact le_stabCenter_of_sup_eq h h3 ⟨⟨hz.1.2, h1⟩, h2⟩

omit [Fintype F] in
theorem c56g_at_of_le (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ S5.vPre h.le a (MSP.qLine l)) (hE2 : IsPGroup 2 E)
    (hErel : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E)
    (hZ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hconc : S5.Concl56 h (2 ^ k) a α' l g x) :
    ZM _ (g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
        ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le)) :=
  c56g_two_of_le h hE hE2 hErel hZ hZ hg hconc

omit [Fintype F] in
theorem c56x_at_of_le (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ S5.vPre h.le a (MSP.qLine l)) (hE2 : IsPGroup 2 E)
    (hErel : (2 ^ k) ^ 2 < (Qv _ (baseA (puAmalgam h.le))).relIndex E)
    (hZ : ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
      Subgroup.centralizer (E : Set (puAmalgam h.le).Universal))
    {g x : (puAmalgam h.le).Universal} (hg : g ∈ stab _ (baseA (puAmalgam h.le)))
    (hx : x ∈ puTrans h.le L (baseA _)) (hconc : S5.Concl56 h (2 ^ k) a α' l g x)
    (hidx : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k) :
    ZM _ (x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) ⊓ ZM _ (baseA (puAmalgam h.le)) ⊓
        ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤ stabCenter _ (baseA (puAmalgam h.le)) :=
  c56x_two_of_le h hE hE2 hErel hZ hZ hg hx hconc hidx

end S5C56

end CFSG.Quasithin.MS93
