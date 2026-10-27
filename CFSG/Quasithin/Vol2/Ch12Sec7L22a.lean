module

public import CFSG.Quasithin.Vol2.Ch12Sec2Inputs
public import CFSG.Quasithin.Background.E3Offender
public import CFSG.Quasithin.Vol2.Ch12Sec7Orb

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem conjSubgroup_eq_of_mem {V : Subgroup G} {l : G}
    (hl : l ∈ Subgroup.normalizer (V : Set G)) : conjSubgroup V l = V :=
  conjSubgroup_eq_iff_mem_normalizer.2 hl

omit [Finite G] in
theorem conj_mem_conjSubgroup {V : Subgroup G} {g l b : G} (hb : b ∈ conjSubgroup V g) :
    l * b * l⁻¹ ∈ conjSubgroup V (g * l⁻¹) := by
  rw [mem_conjSubgroup_iff] at hb ⊢
  rwa [show g * l⁻¹ * (l * b * l⁻¹) * (g * l⁻¹)⁻¹ = g * b * g⁻¹ by group]

theorem conj_z_or_t (h1222 : Stmt12_2_2) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) :
    ∀ v ∈ V, v ≠ 1 → (∃ l ∈ L, l * v * l⁻¹ = z) ∨ (∃ l ∈ L, l * v * l⁻¹ = t) := by
  obtain ⟨z₀, -, t₀, -, h45, h18, horb⟩ := orbits_of_1222 h1222 hS.hyp
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hS.z_mem).1
  have hodd := not_two_dvd_relIndex hS.hyp.hyp hS.T_le_Gz
  obtain ⟨l, hl, hlz⟩ : ∃ l ∈ L, l * z * l⁻¹ = z₀ := by
    rcases horb z hzV hS.z_ne_one with hz | ⟨l, hl, hlz⟩
    · exact hz
    · rw [← hlz, relIndex_centralizer_conj hl] at h18
      exact absurd ⟨9, h18⟩ hodd
  obtain ⟨l', hl', hlt⟩ : ∃ l ∈ L, l * t * l⁻¹ = t₀ := by
    rcases horb t hS.t_mem (ne_one_of_relIndex hS.orbit_t (by decide)) with ⟨l, hl, hlt⟩ | ht
    · rw [← hlt, relIndex_centralizer_conj hl, hS.orbit_t] at h45
      exact absurd h45 (by decide)
    · exact ht
  intro v hv hv1
  rcases horb v hv hv1 with ⟨m, hm, hmv⟩ | ⟨m, hm, hmv⟩
  · refine Or.inl ⟨l⁻¹ * m, L.mul_mem (L.inv_mem hl) hm, ?_⟩
    rw [← hlz] at hmv
    calc l⁻¹ * m * v * (l⁻¹ * m)⁻¹ = l⁻¹ * (m * v * m⁻¹) * l := by group
      _ = l⁻¹ * (l * z * l⁻¹) * l := by rw [hmv]
      _ = z := by group
  · refine Or.inr ⟨l'⁻¹ * m, L.mul_mem (L.inv_mem hl') hm, ?_⟩
    rw [← hlt] at hmv
    calc l'⁻¹ * m * v * (l'⁻¹ * m)⁻¹ = l'⁻¹ * (m * v * m⁻¹) * l' := by group
      _ = l'⁻¹ * (l' * t * l'⁻¹) * l' := by rw [hmv]
      _ = t := by group

theorem pCoreOf_centralizer_le {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) :
    pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf ⟨hS.T_le_Gz, hS.hyp.hyp.sylow.1,
    fun h2 => hS.hyp.hyp.sylow.2 (h2.trans (Subgroup.relIndex_dvd_index_of_le hS.T_le_Gz))⟩

theorem centralizer_t_le_normalizer (h9 : Lemma12_7_9) {T L V : Subgroup G} {t z : G}
    (hS : Setting1274 G T L V t z) :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro c hc
  have h1 : t ∈ conjSubgroup V c := by
    rw [mem_conjSubgroup_iff, Subgroup.mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
    exact hS.t_mem
  exact conjSubgroup_eq_iff_mem_normalizer.1 ((h9 G T L V t hS.toSetting1273).2.2 c h1)

theorem lemma12_7_22_one (h1222 : Stmt12_2_2) (h9 : Lemma12_7_9) (h11 : Lemma12_7_11)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) (g : G)
    (hg : V ⊓ conjSubgroup V g ≠ ⊥) : ⁅V, conjSubgroup V g⁆ = ⊥ := by
  obtain ⟨hcomm, -, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hS.hyp.hyp.irrPlus.2.2.1
  have hVC : V ≤ Subgroup.centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (hcomm.is_comm.comm (⟨y, hy⟩ : ↥V) ⟨x, hx⟩)
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hg
  obtain ⟨hvV, hvVg⟩ := Subgroup.mem_inf.1 hv
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← le_centralizer_iff_comm]
  have hred : ∀ l ∈ L, conjSubgroup V (g * l⁻¹) ≤ Subgroup.centralizer (V : Set G) →
      conjSubgroup V g ≤ Subgroup.centralizer (V : Set G) := by
    intro l hl h b hb
    have h1 := h (conj_mem_conjSubgroup (l := l) hb)
    refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
    have hx' : l * x * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) x).1 hx
    have h2 := Subgroup.mem_centralizer_iff.1 h1 _ hx'
    calc x * b = l⁻¹ * ((l * x * l⁻¹) * (l * b * l⁻¹)) * l := by group
      _ = l⁻¹ * ((l * b * l⁻¹) * (l * x * l⁻¹)) * l := by rw [h2]
      _ = b * x := by group
  rcases conj_z_or_t h1222 hS v hvV hv1' with ⟨l, hl, hlv⟩ | ⟨l, hl, hlv⟩
  · refine hred l hl ?_
    have hzVg : z ∈ conjSubgroup V (g * l⁻¹) := hlv ▸ conj_mem_conjSubgroup hvVg
    have hzV : z ∈ conjSubgroup V 1 := by
      rw [conjSubgroup_one]
      exact (Subgroup.mem_inf.1 hS.z_mem).1
    obtain ⟨c, hc, hce⟩ := (h9 G T L V t hS.toSetting1273).2.1 z
      (Subgroup.mem_inf.1 hS.z_mem).1 1 (g * l⁻¹) hzV hzVg
    rw [hce, one_mul]
    have hVcT : conjSubgroup V c ≤ T := by
      intro x hx
      rw [mem_conjSubgroup_iff] at hx
      have h1 := hS.V_le hx
      have h2 := (Subgroup.mem_normalizer_iff.1
        (le_normalizer_pCoreOf 2 _ (Subgroup.inv_mem _ hc)) _).1 h1
      rw [show c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x by group] at h2
      exact pCoreOf_centralizer_le hS h2
    have hmem : conjSubgroup V c ∈ gammaSet V 0 T := ⟨hVcT, c, le_rfl, mQuot_self _⟩
    exact (le_wClos hmem).trans ((h11 G T L V t hS.toSetting1273).1.trans inf_le_right)
  · refine hred l hl ?_
    have htVg : t ∈ conjSubgroup V (g * l⁻¹) := hlv ▸ conj_mem_conjSubgroup hvVg
    rw [(h9 G T L V t hS.toSetting1273).2.2 _ htVg]
    exact hVC

theorem lemma12_7_22_five (h1222 : Stmt12_2_2) (h9 : Lemma12_7_9) {T L V : Subgroup G}
    {t z : G} (hS : Setting1274 G T L V t z) (g : G)
    (hg : V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) ≠ ⊥) :
    IsPGroup 2 ↥(V ⊔ conjSubgroup V g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomm, hV64, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have hV2 : IsPGroup 2 V := IsPGroup.of_card hV64
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := hS.hyp.hyp.irrPlus.2.2.1
  obtain ⟨⟨v, hv⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hg
  obtain ⟨hvV, hvC⟩ := Subgroup.mem_inf.1 hv
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hred : ∀ l ∈ L, ∀ w : G, l * v * l⁻¹ = w →
      V ≤ pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) → IsPGroup 2 ↥(V ⊔ conjSubgroup V g) := by
    intro l hl w hlw hVw
    have hVgw : conjSubgroup V (g * l⁻¹) ≤ Subgroup.centralizer ({w} : Set G) := by
      intro b hb
      rw [Subgroup.mem_centralizer_singleton_iff, ← hlw]
      have hb' : l⁻¹ * b * l⁻¹⁻¹ ∈ conjSubgroup V (g * l⁻¹ * l⁻¹⁻¹) := conj_mem_conjSubgroup hb
      rw [inv_inv, inv_mul_cancel_right] at hb'
      have h1 := Subgroup.mem_centralizer_iff.1 hvC _ hb'
      calc b * (l * v * l⁻¹) = l * ((l⁻¹ * b * l) * v) * l⁻¹ := by group
        _ = l * (v * (l⁻¹ * b * l)) * l⁻¹ := by rw [h1]
        _ = l * v * l⁻¹ * b := by group
    have hP : IsPGroup 2 ↥(pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) ⊔
        conjSubgroup V (g * l⁻¹)) :=
      IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 _) (isPGroup_conjSubgroup hV2 _)
        (hVgw.trans (le_normalizer_pCoreOf 2 _))
    have hP' : IsPGroup 2 ↥(V ⊔ conjSubgroup V (g * l⁻¹)) := hP.to_le (sup_le_sup_right hVw _)
    have e : conjSubgroup (V ⊔ conjSubgroup V (g * l⁻¹)) l = V ⊔ conjSubgroup V g := by
      unfold conjSubgroup
      rw [Subgroup.map_sup]
      congr 1
      · exact conjSubgroup_eq_of_mem (hLV hl)
      · have := conjSubgroup_conjSubgroup V (g * l⁻¹) l
        unfold conjSubgroup at this
        rw [this, inv_mul_cancel_right]
    rw [← e]
    exact isPGroup_conjSubgroup hP' l
  rcases conj_z_or_t h1222 hS v hvV hv1' with ⟨l, hl, hlv⟩ | ⟨l, hl, hlv⟩
  · exact hred l hl z hlv hS.V_le
  · refine hred l hl t hlv ?_
    have hVt : V ≤ Subgroup.centralizer ({t} : Set G) := fun x hx => by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (hcomm.is_comm.comm (⟨x, hx⟩ : ↥V) ⟨t, hS.t_mem⟩)
    exact le_pCoreOf_of_le_normalizer 2 hVt (centralizer_t_le_normalizer h9 hS) hV2

theorem le_T_of_1222 (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) : V ≤ T := by
  have hy := h.hyp
  obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  exact (hall V hy.irrPlus).1.1

theorem hypE322 (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    HypE322 T V := by
  obtain ⟨-, -, hTV⟩ := card_eq_of_1222 h1222 h
  exact ⟨⟨le_top, h.hyp.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.hyp.sylow.2⟩,
    le_T_of_1222 h1222 h, hTV⟩

theorem isUniqueM_centralizer (h331 : Stmt3_3_1) (h3228 : Stmt3_2_2_eight)
    (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    IsUniqueM (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
      (Subgroup.normalizer (L : Set G)) := by
  have hyp := h.hyp
  obtain ⟨hcomm, -, hTV⟩ := card_eq_of_1222 h1222 h
  have hVT : V ≤ T := le_T_of_1222 h1222 h
  have hV1 : V ≠ ⊥ := hyp.irrPlus.2.1
  have h3 := (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal
    hyp.quasisimple
  rw [hyp.conjClosure_eq] at h3
  obtain ⟨⟨hM, -, huniq⟩, -⟩ := h3
  have hVcl : conjClosure V T = V :=
    le_antisymm (conjClosure_le fun _ ht _ hz => (Subgroup.mem_normalizer_iff.mp (hTV ht) _).mp hz)
      (le_conjClosure V T)
  obtain ⟨-, -, hO⟩ := h3228 G T L V hyp.fsu
  rw [hyp.conjClosure_eq, hVcl] at hO
  have hLT : L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
    rw [← hO]
    exact le_normalizer_pCoreOf 2 _
  have hVQ : V ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
    le_inf hVT fun x hx => Subgroup.mem_centralizer_iff.2 fun y hy =>
      congrArg Subtype.val (hcomm.is_comm.comm (⟨y, hy⟩ : ↥V) ⟨x, hx⟩)
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer
      ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G))
    ⟨T ⊓ Subgroup.centralizer (V : Set G), fun hb => hV1 (le_bot_iff.1 (hb ▸ hVQ)),
      hyp.sylow.1.to_le inf_le_left, rfl⟩
  have hM'eq : M' = Subgroup.normalizer (L : Set G) := huniq M' hM' (hLT.trans hle)
  exact ⟨⟨hM, hM'eq ▸ hle⟩, fun M'' hM'' => huniq M'' hM''.1 (hLT.trans hM''.2)⟩

end S127

end CFSG.Quasithin.H13
