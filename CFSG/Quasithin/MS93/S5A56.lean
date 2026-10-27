module

public import CFSG.Quasithin.MS93.S5AKer
public import CFSG.Quasithin.MS93.S5BXZ
public import CFSG.Quasithin.MS93.S5A53
public import CFSG.Quasithin.MS93.MSPGen3
public import CFSG.Quasithin.MS93.MSPSix

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

namespace S5

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {k : ℕ} {F : Type} [Field F]
  [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Dict

variable (hTM : T ≤ M)

omit [Finite G] [Fintype F] in
theorem vIm_le_of_le_vPre' {Y : Subgroup ↥(StatedSp 2 F)} {K : Subgroup (puAmalgam hTM).Universal}
    (hK : K ≤ vPre hTM a Y) : vIm hTM a K ≤ Y := by
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨m', hm', he⟩ := hK hm
  rw [(puAmalgam hTM).ofA_injective he] at hm'
  exact hm'

omit [Finite G] [Fintype F] in
theorem vIm_map_conj (m : ↥M) (K : Subgroup (puAmalgam hTM).Universal) :
    vIm hTM a (K.map (MulAut.conj ((puAmalgam hTM).ofA m)).toMonoidHom) =
      (vIm hTM a K).map (MulAut.conj (a m)).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨n, ⟨z, hz, hzn⟩, rfl⟩
    refine ⟨a (m⁻¹ * n * m), ⟨m⁻¹ * n * m, ?_, rfl⟩, ?_⟩
    · change (puAmalgam hTM).ofA (m⁻¹ * n * m) ∈ K
      have e : z = (puAmalgam hTM).ofA (m⁻¹ * n * m) := by
        have h1 : (puAmalgam hTM).ofA m * z * ((puAmalgam hTM).ofA m)⁻¹ =
            (puAmalgam hTM).ofA n := hzn
        rw [map_mul, map_mul, map_inv, ← h1]
        group
      rw [← e]
      exact hz
    · change a m * a (m⁻¹ * n * m) * (a m)⁻¹ = a n
      rw [map_mul, map_mul, map_inv]
      group
  · rintro ⟨y', ⟨n, hn, rfl⟩, rfl⟩
    refine ⟨m * n * m⁻¹, ⟨(puAmalgam hTM).ofA n, hn, ?_⟩, ?_⟩
    · change (puAmalgam hTM).ofA m * (puAmalgam hTM).ofA n * ((puAmalgam hTM).ofA m)⁻¹ =
        (puAmalgam hTM).ofA (m * n * m⁻¹)
      rw [map_mul, map_mul, map_inv]
    · change a (m * n * m⁻¹) = a m * a n * (a m)⁻¹
      rw [map_mul, map_mul, map_inv]

omit [Finite G] [Fintype F] in
theorem vIm_sup {K K' : Subgroup (puAmalgam hTM).Universal}
    (hK : K ≤ (puAmalgam hTM).ofA.range) (hK' : K' ≤ (puAmalgam hTM).ofA.range) :
    vIm hTM a (K ⊔ K') = vIm hTM a K ⊔ vIm hTM a K' := by
  rw [vIm, vIm, vIm, ← Subgroup.comap_sup_eq_of_le_range _ hK hK', Subgroup.map_sup]

omit [Finite G] [Fintype F] in
theorem ofA_range_eq : (puAmalgam hTM).ofA.range = stab (puAmalgam hTM) (baseA _) := by
  rw [puAmalgam.stab_baseA, imM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]

end Dict

section ImL

omit [Fintype F] in
theorem imSp_L_le_commutator (h : PUHyp M T L) :
    imSp a L ≤ commutator (StatedSp 2 F) := by
  have hL : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.2 h.perfect
  set f := a.comp (Subgroup.inclusion h.L_le)
  have hf : f.range = imSp a L := by
    rw [imSp, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hr : Group.IsPerfect ↥f.range := Group.IsPerfect.range f
  rw [← hf, ← Subgroup.commutator_eq_self (H := f.range)]
  exact Subgroup.commutator_mono le_top le_top

theorem commutator_le_imSp_L (h : PUHyp M T L) (hd : IsSp4Data M T L k F a) :
    commutator (StatedSp 2 F) ≤ imSp a L := by
  rcases Nat.lt_or_ge k 2 with hk | hk
  · have hk1 : k = 1 := by have := hd.1; omega
    have hq : Nat.card F = 2 := by rw [hd.nat_card_eq, hk1]; rfl
    obtain ⟨c⟩ := MSP.nonempty_ringEquiv_of_card_two hq
    have hLn : (L.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
    have hN : (imSp a L).Normal := hLn.map a hd.surj
    have hN' : (Subgroup.map a (L.subgroupOf M)).Normal := hN
    have h3 : ∀ g : ↥(StatedSp 2 F), g ^ 3 = 1 → g ∈ imSp a L := by
      intro g hg3
      obtain ⟨m, rfl⟩ := hd.surj g
      have hsup : L.subgroupOf M ⊔ T.subgroupOf M = ⊤ := by
        rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
      have hm : m ∈ L.subgroupOf M ⊔ T.subgroupOf M := by rw [hsup]; exact Subgroup.mem_top _
      obtain ⟨l, hl, t, ht, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hm
      obtain ⟨e, he⟩ := h.isPGroup ⟨(t : G), ht⟩
      have ht' : t ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
      refine mem_of_pow_mem_of_coprime (S := imSp a L) (p := 3) (q := 2 ^ e)
        (Nat.Coprime.pow_right _ (by norm_num)) (by rw [hg3]; exact one_mem _) ?_
      have hl1 : (QuotientGroup.mk' (imSp a L)) (a l) = 1 :=
        (QuotientGroup.eq_one_iff (a l)).2 (Subgroup.mem_map_of_mem a hl)
      have hπ : (QuotientGroup.mk' (imSp a L)) (a (l * t) ^ 2 ^ e) = 1 := by
        rw [map_pow, map_mul, map_mul, hl1, one_mul, ← map_pow, ← map_pow, ht', map_one,
          map_one]
      exact (QuotientGroup.eq_one_iff _).1 hπ
    intro g hg
    rw [MSP.mem_commutator_iff_sign c] at hg
    have hσ : (B5FinSp.theta c).symm g ∈ alternatingGroup (Fin 6) := hg
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating] at hσ
    have hle : Subgroup.closure {σ : Equiv.Perm (Fin 6) | σ.IsThreeCycle} ≤
        (imSp a L).comap (B5FinSp.theta c).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro σ hσ3
      refine h3 _ ?_
      change (B5FinSp.theta c σ) ^ 3 = 1
      rw [← map_pow, ← hσ3.orderOf, pow_orderOf_eq_one, map_one]
    have := hle hσ
    simpa using this
  · rw [imSp, S5B.map_L_eq_top h hd hk]
    exact le_top

end ImL

section Lift

variable (h : PUHyp M T L)

theorem vIm_vPre (hd : IsSp4Data M T L k F a) (Y : Subgroup ↥(StatedSp 2 F)) :
    vIm h.le a (vPre h.le a Y) = Y := by
  rw [vIm, vPre, Subgroup.comap_map_eq_self_of_injective (puAmalgam h.le).ofA_injective,
    Subgroup.map_comap_eq_self_of_surjective hd.surj]

omit [Fintype F] in
theorem vPre_le_stab (Y : Subgroup ↥(StatedSp 2 F)) :
    vPre h.le a Y ≤ stab (puAmalgam h.le) (baseA _) := by
  rw [← ofA_range_eq]
  exact Subgroup.map_le_range _ _

theorem qv_le_vPre (hd : IsSp4Data M T L k F a) (Y : Subgroup ↥(StatedSp 2 F)) :
    Qv (puAmalgam h.le) (baseA _) ≤ vPre h.le a Y := by
  rw [qv_baseA_eq h]
  refine imM_le_vPre h fun y hy => ?_
  obtain ⟨m, hm, rfl⟩ := hy
  have := ((mem_kerG a).1 (hd.pCoreOf_le_kerG h (Subgroup.mem_subgroupOf.1 hm))).2
  rw [show (⟨(m : G), _⟩ : ↥M) = m from rfl] at this
  rw [this]
  exact one_mem Y

omit [Fintype F] in
theorem rconj_le_stab {K : Subgroup (puAmalgam h.le).Universal}
    (hK : K ≤ stab (puAmalgam h.le) (baseA _)) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab (puAmalgam h.le) (baseA _)) : rconj g K ≤ stab (puAmalgam h.le) (baseA _) := by
  rintro _ ⟨y, hy, rfl⟩
  exact mul_mem (mul_mem (inv_mem hg) (hK hy)) (inv_mem (inv_mem hg))

theorem qv_le_rconj {K : Subgroup (puAmalgam h.le).Universal}
    (hK : Qv (puAmalgam h.le) (baseA _) ≤ K) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab (puAmalgam h.le) (baseA _)) : Qv (puAmalgam h.le) (baseA _) ≤ rconj g K := by
  intro q hq
  refine ⟨g * q * g⁻¹, hK ?_, by change g⁻¹ * (g * q * g⁻¹) * g⁻¹⁻¹ = q; group⟩
  exact (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_qv _ _ hg) q).1 hq

theorem lift56 (hd : IsSp4Data M T L k F a) {K : Subgroup (puAmalgam h.le).Universal}
    (hK : K ≤ stab (puAmalgam h.le) (baseA _)) (hQK : Qv (puAmalgam h.le) (baseA _) ≤ K) :
    (imSp a L ≤ vIm h.le a K → puTrans h.le L (baseA _) ≤ K) ∧
      (vIm h.le a K = ⊤ → K = stab (puAmalgam h.le) (baseA _)) := by
  rw [puAmalgam.stab_baseA] at hK
  obtain ⟨K', -, hK'M, rfl⟩ := exists_eq_imM h.le hK
  have hQK' : pCoreOf 2 M ≤ K' := by
    rw [qv_baseA_eq h] at hQK
    exact (imM_le_imM_iff h.le (pCoreOf_le' M)).1 hQK
  rw [vIm_imM h]
  refine ⟨fun hL => ?_, fun htop => ?_⟩
  · rw [puTrans_L_baseA h]
    exact imM_mono h.le (hd.L_le_of_imSp_le h hQK' hL)
  · rw [puAmalgam.stab_baseA, hd.eq_of_imSp_eq h hK'M hQK' (htop ▸ le_top)]

theorem card_vIm (hd : IsSp4Data M T L k F a) {E : Subgroup (puAmalgam h.le).Universal}
    (hE : E ≤ stab (puAmalgam h.le) (baseA _)) (hE2 : IsPGroup 2 E) :
    Nat.card (vIm h.le a E) = (Qv (puAmalgam h.le) (baseA _)).relIndex E := by
  rw [puAmalgam.stab_baseA] at hE
  obtain ⟨E', -, hE'M, rfl⟩ := exists_eq_imM h.le hE
  have hE'2 : IsPGroup 2 E' := fun x => by
    obtain ⟨n, hn⟩ := hE2 ⟨(puAmalgam h.le).ofA ⟨x, hE'M x.2⟩, ⟨x, hE'M x.2⟩,
      Subgroup.mem_subgroupOf.2 x.2, rfl⟩
    refine ⟨n, Subtype.ext ?_⟩
    have h1 : (puAmalgam h.le).ofA (⟨x, hE'M x.2⟩ ^ 2 ^ n) = (puAmalgam h.le).ofA 1 := by
      rw [map_pow, map_one]
      simpa using congrArg Subtype.val hn
    have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
    simpa using h2
  rw [vIm_imM h, qv_baseA_eq h, relIndex_imM h.le hE'M, hd.card_imSp_of_isPGroup h hE'2 hE'M]

end Lift

section Concl

variable (h : PUHyp M T L)

omit [Fintype F] in
theorem vIm_mono' {K K' : Subgroup (puAmalgam h.le).Universal} (hKK' : K ≤ K') :
    vIm h.le a K ≤ vIm h.le a K' :=
  Subgroup.map_mono (Subgroup.comap_mono hKK')

theorem concl56_of (hd : IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    {l : Submodule F (MSP.V4 F)} (hl : MSP.IsLine l)
    (hZ : zHat _ (baseA (puAmalgam h.le)) α' ≤ stab (puAmalgam h.le) (baseA _))
    (hJ : jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _) ≤ stab (puAmalgam h.le) (baseA _))
    (hQJ : Qv (puAmalgam h.le) (baseA _) ≤ jOff h.le L (2 ^ k) (baseA (puAmalgam h.le)) (baseB _))
    {g₀ x₀ : ↥(StatedSp 2 F)} (hx₀ : x₀ ∈ commutator (StatedSp 2 F))
    (hopp : l.map (Matrix.mulVecLin (MSP.mat g₀⁻¹)) ⊓ l = ⊥)
    (hopp' : (l.map (Matrix.mulVecLin (MSP.mat g₀⁻¹))).map (Matrix.mulVecLin (MSP.mat x₀⁻¹)) ⊓
      l.map (Matrix.mulVecLin (MSP.mat g₀⁻¹)) = ⊥)
    (hc : commutator (StatedSp 2 F) ≤
      (vIm h.le a (jOff h.le L (2 ^ k) (baseA _) (baseB _))).map (MulAut.conj g₀⁻¹).toMonoidHom ⊔
        vIm h.le a (zHat _ (baseA _) α') ⊔
        (vIm h.le a (zHat _ (baseA _) α')).map (MulAut.conj x₀).toMonoidHom)
    (hdq : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k → x₀ ∈ MSP.stab l) :
    ∃ g ∈ stab _ (baseA (puAmalgam h.le)), ∃ x ∈ puTrans h.le L (baseA _),
      Concl56 h (2 ^ k) a α' l g x := by
  have := hd.charP
  obtain ⟨m₀, rfl⟩ := hd.surj g₀
  obtain ⟨y, hyL, rfl⟩ := commutator_le_imSp_L h hd hx₀
  have hst : stab (puAmalgam h.le) (baseA _) = (puAmalgam h.le).ofA.range :=
    (ofA_range_eq h.le).symm
  have hgst : (puAmalgam h.le).ofA m₀ ∈ stab (puAmalgam h.le) (baseA _) := hst ▸ ⟨m₀, rfl⟩
  have hxL : (puAmalgam h.le).ofA y ∈ puTrans h.le L (baseA _) := by
    rw [puTrans_L_baseA h]
    exact ⟨y, hyL, rfl⟩
  have hconj : ∀ (m : ↥M) (K : Subgroup (puAmalgam h.le).Universal),
      vIm h.le a (rconj ((puAmalgam h.le).ofA m) K) =
        (vIm h.le a K).map (MulAut.conj (a m)⁻¹).toMonoidHom := fun m K => by
    rw [rconj, ← map_inv, vIm_map_conj h.le m⁻¹ K, map_inv]
  have hQ₁ := vPre_le_stab (a := a) h (MSP.qLine l)
  have hl₁ : MSP.IsLine (l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))) := MSP.isLine_map hl _
  have hl₂ : MSP.IsLine ((l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))).map
      (Matrix.mulVecLin (MSP.mat (a y)⁻¹))) := MSP.isLine_map hl₁ _
  have hvQ₁ : vIm h.le a (rconj ((puAmalgam h.le).ofA m₀) (vPre h.le a (MSP.qLine l))) =
      MSP.qLine (l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))) := by
    rw [hconj, vIm_vPre h hd, MSP.qLine_map]
  refine ⟨(puAmalgam h.le).ofA m₀, hgst, (puAmalgam h.le).ofA y, hxL, ?_, ?_, ?_, ?_⟩
  ·
    intro E₁ E₂ hE₁2 hE₂2 hE₁ hE₂ hE₁c hE₂c
    have hE₁st : E₁ ≤ stab (puAmalgam h.le) (baseA _) := hE₁.trans (rconj_le_stab h hQ₁ hgst)
    have hE₂st : E₂ ≤ stab (puAmalgam h.le) (baseA _) := hE₂.trans hQ₁
    have hv₁ : vIm h.le a E₁ ≤ MSP.qLine (l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))) :=
      hvQ₁ ▸ vIm_mono' h hE₁
    have hv₂ : vIm h.le a E₂ ≤ MSP.qLine l := (vIm_vPre h hd (MSP.qLine l)) ▸ vIm_mono' h hE₂
    have htop := MSP.sup_eq_top_of_le_qLine hl₁ hl hopp hv₁ hv₂
      (by rw [card_vIm h hd hE₁st hE₁2, hd.nat_card_eq]; exact hE₁c)
      (by rw [card_vIm h hd hE₂st hE₂2, hd.nat_card_eq]; exact hE₂c)
    have hK : E₁ ⊔ E₂ ⊔ Qv (puAmalgam h.le) (baseA _) ≤ stab (puAmalgam h.le) (baseA _) :=
      sup_le (sup_le hE₁st hE₂st) (qv_le_stab _ _)
    refine (lift56 h hd hK le_sup_right).2 (eq_top_iff.2 ?_)
    rw [← htop]
    exact sup_le (vIm_mono' h (le_sup_left.trans le_sup_left))
      (vIm_mono' h (le_sup_right.trans le_sup_left))
  ·
    have hxst : (puAmalgam h.le).ofA y ∈ stab (puAmalgam h.le) (baseA _) := hst ▸ ⟨y, rfl⟩
    have hK₁ : rconj ((puAmalgam h.le).ofA m₀) (vPre h.le a (MSP.qLine l)) ≤
        stab (puAmalgam h.le) (baseA _) := rconj_le_stab h hQ₁ hgst
    have hK₂ : rconj ((puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y)
        (vPre h.le a (MSP.qLine l)) ≤ stab (puAmalgam h.le) (baseA _) :=
      rconj_le_stab h hQ₁ (mul_mem hgst hxst)
    have hvK₂ : vIm h.le a (rconj ((puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y)
        (vPre h.le a (MSP.qLine l))) =
        MSP.qLine ((l.map (Matrix.mulVecLin (MSP.mat (a m₀)⁻¹))).map
          (Matrix.mulVecLin (MSP.mat (a y)⁻¹))) := by
      rw [show (puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y = (puAmalgam h.le).ofA (m₀ * y)
        from (map_mul _ _ _).symm, hconj, vIm_vPre h hd, MSP.qLine_map, MSP.qLine_map,
        MSP.map_conj_map_conj, map_mul, _root_.mul_inv_rev]
    have htop := MSP.qLine_sup_qLine_eq_top hl₂ hl₁ hopp'
    have hK : rconj ((puAmalgam h.le).ofA m₀) (vPre h.le a (MSP.qLine l)) ⊔
        rconj ((puAmalgam h.le).ofA m₀ * (puAmalgam h.le).ofA y) (vPre h.le a (MSP.qLine l)) =
        stab (puAmalgam h.le) (baseA _) := by
      refine (lift56 h hd (sup_le hK₁ hK₂) (le_sup_left.trans' (qv_le_rconj h
        (qv_le_vPre h hd _) hgst))).2 (eq_top_iff.2 ?_)
      rw [← htop]
      exact sup_le (hvK₂ ▸ vIm_mono' h le_sup_right) (hvQ₁ ▸ vIm_mono' h le_sup_left)
    rintro z ⟨⟨hzZ, hz₁⟩, hz₂⟩
    have hzst : z ∈ stab (puAmalgam h.le) (baseA _) :=
      (zm_le_qv_self _ (isMVtx_baseA _) h.critDist_pos |>.trans (qv_le_stab _ _)) hzZ
    have hle : stab (puAmalgam h.le) (baseA _) ≤ Subgroup.centralizer {z} := by
      rw [← hK]
      refine sup_le (fun w hw => ?_) (fun w hw => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hz₁ w hw)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (Subgroup.mem_centralizer_iff.1 hz₂ w hw)
    refine ⟨⟨z, hzst⟩, Subgroup.mem_center_iff.2 fun w => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle w.2)
  ·
    have hxinv : ((puAmalgam h.le).ofA y)⁻¹ ∈ stab (puAmalgam h.le) (baseA _) :=
      inv_mem (hst ▸ ⟨y, rfl⟩)
    have hH : rconj ((puAmalgam h.le).ofA m₀) (jOff h.le L (2 ^ k) (baseA _) (baseB _)) ⊔
        zHat _ (baseA _) α' ⊔ rconj ((puAmalgam h.le).ofA y)⁻¹ (zHat _ (baseA _) α') ≤
        stab (puAmalgam h.le) (baseA _) :=
      sup_le (sup_le (rconj_le_stab h hJ hgst) hZ) (rconj_le_stab h hZ hxinv)
    have hQH : Qv (puAmalgam h.le) (baseA _) ≤
        rconj ((puAmalgam h.le).ofA m₀) (jOff h.le L (2 ^ k) (baseA _) (baseB _)) ⊔
        zHat _ (baseA _) α' ⊔ rconj ((puAmalgam h.le).ofA y)⁻¹ (zHat _ (baseA _) α') :=
      (qv_le_rconj h hQJ hgst).trans (le_sup_left.trans le_sup_left)
    refine (lift56 h hd hH hQH).1 ((imSp_L_le_commutator h).trans (hc.trans ?_))
    refine sup_le (sup_le ?_ (vIm_mono' h (le_sup_right.trans le_sup_left))) ?_
    · rw [← hconj]
      exact vIm_mono' h (le_sup_left.trans le_sup_left)
    · have e : rconj ((puAmalgam h.le).ofA y)⁻¹ (zHat _ (baseA _) α') =
          (zHat _ (baseA _) α').map (MulAut.conj ((puAmalgam h.le).ofA y)).toMonoidHom := by
        rw [rconj, inv_inv]
      rw [← vIm_map_conj h.le y, ← e]
      exact vIm_mono' h le_sup_right
  · intro hrel
    exact ⟨y, hdq hrel, rfl⟩

end Concl

section Quad

theorem commSp_le_fixSp_of_quad (hd : IsSp4Data M T L k F a) (h : PUHyp M T L)
    {Z : Subgroup G}
    (hcomm : ∀ z ∈ Z, ∀ u ∈ Uq M T L, z * u * z⁻¹ * u⁻¹ ∈ Z)
    (hab : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z) :
    MSP.commSp (imSp a Z) ≤ MSP.fixSp (imSp a Z) := by
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  refine MSP.commSp_le_iff.2 ?_
  rintro _ ⟨⟨z, hzM'⟩, hz, rfl⟩ v
  have hz' : z ∈ Z := Subgroup.mem_subgroupOf.1 hz
  obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd v)
  have hv : nv.vec u = v := by rw [NatVec.vec, hu]; rfl
  have hzu : z * u * z⁻¹ ∈ Uq M T L := (Subgroup.mem_normalizer_iff.1 (hUn hzM') u).1 u.2
  set c : ↥(Uq M T L) := ⟨z * u * z⁻¹, hzu⟩ * u⁻¹
  have hcv : nv.vec c = MSP.mat (a ⟨z, hzM'⟩) *ᵥ v - v := by
    rw [nv.vec_mul, nv.vec_inv, nv.vec_conj ⟨z, hzM'⟩ u hzu, hv, sub_eq_add_neg]
  have hcZ : (c : G) ∈ Z := hcomm z hz' u u.2
  rw [← hcv]
  refine nv.vec_mem_fixSp c (Subgroup.mem_centralizer_iff.2 fun z' hz'' => ?_)
  exact hab z' hz'' c hcZ

end Quad

section ZAlpha

variable (h : PUHyp M T L)

theorem zm_le_qv_baseB {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hβ : geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _) :
    ZM (puAmalgam h.le) α' ≤ Qv _ (baseB (puAmalgam h.le)) :=
  hβ ▸ zm_le_qv_geo_one _ h.hyp20 h.critDist_pos hc

omit [Finite G] in
theorem zHat_eq_of_not {X : GoldAmalgam (↥M) (↥T) (Hol ↥T)} {α α' : Vtx X}
    (hno : ¬ ∃ t₁ t₂ t₃, IsHatTriple X α α' t₁ t₂ t₃ ∧
      t₃ ∉ Subgroup.closure ({t₁, t₂} : Set X.Universal) ⊔ Qv X α') :
    zHat X α α' = ZM X α' := by
  refine le_antisymm inf_le_left (le_inf le_rfl (le_iInf fun t => le_iInf fun ht =>
    le_iInf fun hn => ?_))
  exact absurd ⟨t.1, t.2.1, t.2.2, ht, hn⟩ hno

theorem commSp_le_fixSp_zm (hd : IsSp4Data M T L k F a) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical _ (baseA (puAmalgam h.le)) α') :
    MSP.commSp (vIm h.le a (ZM _ α')) ≤ MSP.fixSp (vIm h.le a (ZM _ α')) := by
  have hb0 := h.critDist_pos
  have hst : ZM (puAmalgam h.le) α' ≤ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact zm_le_stab_of_isCritical _ h.hyp20 hb0 hc
  obtain ⟨Z', -, hZ'M, hZ'⟩ := exists_eq_imM h.le hst
  rw [hZ', vIm_imM h]
  have hcr' := ms22_iii _ h.hyp20 hb0 h.centHyp hc
  have hZαst : ZM (puAmalgam h.le) (baseA _) ≤ stab _ α' :=
    zm_le_stab_of_isCritical _ h.hyp20 hb0 hcr'
  have hRZ : ⁅ZM (puAmalgam h.le) α', ZM (puAmalgam h.le) (baseA _)⁆ ≤ ZM _ α' :=
    commutator_le_left_of_le_normalizer (hZαst.trans (stab_le_normalizer_zm _ _))
  have hab := (isElemAbelian_zm _ h.hyp20 hb0 (hc.isMVtx_right _ h.hyp20)).1
  refine commSp_le_fixSp_of_quad hd h (fun z hz u hu => ?_) (fun z hz z' hz' => ?_)
  · have hzM := hZ'M hz
    have huM : u ∈ M := (Uq_le h.L_le) hu
    have hmem : (puAmalgam h.le).ofA ⟨z * u * z⁻¹ * u⁻¹, by
        exact M.mul_mem (M.mul_mem (M.mul_mem hzM huM) (M.inv_mem hzM)) (M.inv_mem huM)⟩ ∈
        ZM (puAmalgam h.le) α' := by
      refine hRZ ?_
      have h1 : (puAmalgam h.le).ofA ⟨z, hzM⟩ ∈ ZM (puAmalgam h.le) α' :=
        hZ' ▸ ⟨⟨z, hzM⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
      have h2 : (puAmalgam h.le).ofA ⟨u, huM⟩ ∈ ZM (puAmalgam h.le) (baseA _) := by
        rw [puAmalgam.zm_baseA]
        exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.2 (Uq_le_Z0q h.L_le hu), rfl⟩
      have := Subgroup.commutator_mem_commutator h1 h2
      rw [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul] at this
      exact this
    rw [hZ'] at hmem
    obtain ⟨w, hw, hwe⟩ := hmem
    have e := (puAmalgam h.le).ofA_injective hwe
    rw [e] at hw
    exact Subgroup.mem_subgroupOf.1 hw
  · have h1 : (puAmalgam h.le).ofA ⟨z, hZ'M hz⟩ ∈ ZM (puAmalgam h.le) α' :=
      hZ' ▸ ⟨⟨z, hZ'M hz⟩, Subgroup.mem_subgroupOf.2 hz, rfl⟩
    have h2 : (puAmalgam h.le).ofA ⟨z', hZ'M hz'⟩ ∈ ZM (puAmalgam h.le) α' :=
      hZ' ▸ ⟨⟨z', hZ'M hz'⟩, Subgroup.mem_subgroupOf.2 hz', rfl⟩
    have := hab.is_comm.comm (⟨_, h1⟩ : ↥(ZM (puAmalgam h.le) α')) ⟨_, h2⟩
    have := congrArg Subtype.val this
    simp only [Subgroup.coe_mul] at this
    rw [← map_mul, ← map_mul] at this
    exact congrArg Subtype.val ((puAmalgam h.le).ofA_injective this)

end ZAlpha

end S5

end CFSG.Quasithin.MS93
