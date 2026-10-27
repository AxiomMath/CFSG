module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34DA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvSupInf
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S34Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure DSit (H M S : Subgroup G) (δ μ γ γ' : Geo H M) : Prop where
  hG : Glob H M S
  hδ : vtype δ = false
  T : Tri μ δ γ γ'

def D1 (δ γ : Geo H M) : Subgroup G := Cb δ ⊓ Zv γ

def Ub (δ γ : Geo H M) : Subgroup G := Subgroup.centralizer (D1 δ γ : Set G) ⊓ stab δ

omit [Finite G] in
theorem stab_le_normQv (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Qv δ : Set G) :=
  le_normalizer_pCoreOf 2 (stab δ)

def Yb (δ γ : Geo H M) (q : G) : Subgroup G :=
  D1 δ γ ⊔ (D1 δ γ).map (MulAut.conj q).toMonoidHom

omit [Finite G] in
theorem mem_map_conj {K : Subgroup G} {q y : G} :
    y ∈ K.map (MulAut.conj q).toMonoidHom ↔ ∃ x ∈ K, y = q * x * q⁻¹ := by
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  exact ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩, fun ⟨x, hx, h⟩ => ⟨x, hx, h.symm⟩⟩

omit [Finite G] in
theorem conj_mem_Yb {δ γ : Geo H M} {q x : G} (hx : x ∈ D1 δ γ) : q * x * q⁻¹ ∈ Yb δ γ q :=
  Subgroup.mem_sup_right (mem_map_conj.mpr ⟨x, hx, rfl⟩)

omit [Finite G] in
theorem mem_Yb_left {δ γ : Geo H M} {q x : G} (hx : x ∈ D1 δ γ) : x ∈ Yb δ γ q :=
  Subgroup.mem_sup_left hx

omit [Finite G] in
theorem exists_mul_of_mem_sup {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  let W : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, x = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, (mul_one 1).symm⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        have h := hc a' ha' b hb
        calc a * b * (a' * b') = a * (b * a') * b' := by group
          _ = a * (a' * b) * b' := by rw [← h]
          _ = a * a' * (b * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h := hc a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
        rw [mul_inv_rev, h] }
  have hle : A ⊔ B ≤ W := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, (mul_one a).symm⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, (one_mul b).symm⟩)
  exact hle hx

omit [Finite G] in
theorem D1_le_Zγ {δ γ : Geo H M} : D1 δ γ ≤ Zv γ := inf_le_right

omit [Finite G] in
theorem D1_le_Cb {δ γ : Geo H M} : D1 δ γ ≤ Cb δ := inf_le_left

omit [Finite G] in
theorem L_comm {δ : Geo H M} {l x : G} (hl : l ∈ oTwoRes (stab δ)) (hx : x ∈ Cb δ) :
    x * l = l * x :=
  (Subgroup.mem_centralizer_iff.mp hx.2 l hl).symm

omit [Finite G] in
theorem L_le_U {δ γ : Geo H M} : oTwoRes (stab δ) ≤ Ub δ γ := by
  intro l hl
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, oTwoRes_le _ hl⟩
  exact L_comm hl (D1_le_Cb hx)

namespace DSit

variable {δ μ γ γ' : Geo H M} (hs : DSit H M S δ μ γ γ')
include hs

theorem hA : F53Amalgam H M S := hs.hG.amalg

theorem adj : (graph (H ⊔ M) H M).Adj μ δ := hs.T.ha

theorem nδ : δ ∈ nbrs μ := hs.T.ha

theorem nμ : μ ∈ nbrs δ := nbrs_symm hs.T.ha

theorem nγ : γ ∈ nbrs μ := hs.T.hb

theorem vμ : vtype μ = true := by
  have h := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from hs.nμ)
  rw [hs.hδ] at h
  cases hv : vtype μ
  · exact absurd hv.symm h
  · rfl

theorem vγ : vtype γ = false := S42B1.vtype_false_of_nbr hs.vμ hs.T.hb

theorem zδ : Zv δ ≤ centerOf (stab δ) := hs.hG.central δ hs.hδ

theorem zγ : Zv γ ≤ centerOf (stab γ) := hs.hG.central γ hs.vγ

theorem Zδμ : Zv δ ≤ Zv μ := (Zv_eq_omegaOneCenter_inf hs.hA hs.nμ hs.zδ).2

theorem Zγμ : Zv γ ≤ Zv μ :=
  (Zv_eq_omegaOneCenter_inf hs.hA (nbrs_symm hs.T.hb) hs.zγ).2

theorem Zsup : Zv δ ⊔ Zv γ = Zv μ ∧ Zv δ ⊓ Zv γ = ⊥ :=
  EmptyFaithful.Stellmacher.OrdinaryProofs.Zv_sup_eq_and_inf_eq_bot hs.hA hs.vμ
    (hs.hG.crit μ hs.vμ) hs.T.ha hs.T.hb hs.T.hab hs.zδ

theorem sylowE : IsSylowTwoOf (stab μ ⊓ stab δ) (stab δ) := by
  rw [inf_comm]; exact sylow_stab_inf_left hs.hA hs.nμ

theorem stab_le_sup : stab δ ≤ oTwoRes (stab δ) ⊔ (stab μ ⊓ stab δ) :=
  le_oTwoRes_sup_of_isSylowTwoOf hs.sylowE

theorem prod : Qv μ ⊔ Qv δ = stab μ ⊓ stab δ := hs.hG.prod μ δ hs.adj hs.vμ

theorem idx : (Qv μ).relIndex (stab μ ⊓ stab δ) = 2 :=
  relIndex_Qv_inf_true hs.hA hs.nδ hs.vμ

theorem idxγ : (Qv μ).relIndex (stab μ ⊓ stab γ) = 2 :=
  relIndex_Qv_inf_true hs.hA hs.nγ hs.vμ

theorem Qμ_le_E : Qv μ ≤ stab μ ⊓ stab δ :=
  le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hs.hA hs.nδ)

theorem Qδ_le_E : Qv δ ≤ stab μ ⊓ stab δ :=
  le_inf (Qv_le_stab_of_mem_nbrs hs.hA hs.nμ) (pCoreOf_le 2 _)

theorem D1_le_Zμ : D1 δ γ ≤ Zv μ := D1_le_Zγ.trans hs.Zγμ

theorem Qμ_comm {k x : G} (hk : k ∈ Qv μ) (hx : x ∈ Zv μ) : x * k = k * x :=
  Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hs.hA μ hk) x hx

theorem stabγ_comm {t x : G} (ht : t ∈ stab γ) (hx : x ∈ Zv γ) : x * t = t * x :=
  (Subgroup.mem_centralizer_iff.mp (hs.zγ hx).2 t ht).symm

theorem Qμ_le_U : Qv μ ≤ Ub δ γ := by
  intro k hk
  refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, hs.Qμ_le_E hk |>.2⟩
  exact hs.Qμ_comm hk (hs.D1_le_Zμ hx)

theorem cent_edge (hne : D1 δ γ ≠ ⊥) {s : G} (hsE : s ∈ stab μ ⊓ stab δ)
    (hc : ∀ x ∈ D1 δ γ, s * x = x * s) : s ∈ Qv μ := by
  by_contra hsQ
  have hQK : Qv μ ≤ Subgroup.centralizer (D1 δ γ : Set G) ⊓ stab μ := by
    intro k hk
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, pCoreOf_le 2 _ hk⟩
    exact hs.Qμ_comm hk (hs.D1_le_Zμ hx)
  have hKγ : stab μ ⊓ stab γ ≤ Subgroup.centralizer (D1 δ γ : Set G) ⊓ stab μ := by
    intro t ht
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, ht.1⟩
    exact hs.stabγ_comm ht.2 (D1_le_Zγ hx)
  have hsK : s ∈ Subgroup.centralizer (D1 δ γ : Set G) ⊓ stab μ := by
    refine ⟨Subgroup.mem_centralizer_iff.mpr fun x hx => ?_, hsE.1⟩
    exact (hc x hx).symm
  have hKE : stab μ ⊓ stab δ ≤ Subgroup.centralizer (D1 δ γ : Set G) ⊓ stab μ := by
    intro e he
    by_cases heQ : e ∈ Qv μ
    · exact hQK heQ
    · have hk : e * s⁻¹ ∈ Qv μ :=
        F53B3.O1.mul_inv_mem_of_relIndex_two hs.idx he hsE heQ hsQ
      have : e = (e * s⁻¹) * s := by group
      rw [this]
      exact mul_mem (hQK hk) hsK
  have hμK : stab μ ≤ Subgroup.centralizer (D1 δ γ : Set G) ⊓ stab μ := by
    have hsup := sup_edges_eq_stab hs.hA hs.vμ hs.nδ hs.nγ hs.T.hab
    intro g hg
    rw [← hsup] at hg
    exact sup_le hKE hKγ hg
  have hD1le : D1 δ γ ≤ stab μ ⊓ stab γ := D1_le_Zγ.trans (Zv_le_edge hs.hA hs.nγ)
  refine hne (eq_bot_of_normalizes_both hs.hA (show (graph (H ⊔ M) H M).Adj μ γ from hs.nγ)
    hD1le ?_ ?_)
  · intro g hg
    refine mem_normalizer_of_comm fun y hy => ?_
    exact ((Subgroup.mem_centralizer_iff.mp (hμK hg).1 y hy)).symm
  · intro g hg
    refine mem_normalizer_of_comm fun y hy => ?_
    exact (hs.stabγ_comm hg (D1_le_Zγ hy)).symm

theorem U_inf_Qδ (hne : D1 δ γ ≠ ⊥) : Ub δ γ ⊓ Qv δ = Qv μ ⊓ Qv δ := by
  refine le_antisymm ?_ (le_inf (fun x hx => hs.Qμ_le_U hx.1) inf_le_right)
  rintro x ⟨hxU, hxQ⟩
  refine ⟨hs.cent_edge hne (hs.Qδ_le_E hxQ) fun y hy => ?_, hxQ⟩
  exact (Subgroup.mem_centralizer_iff.mp hxU.1 y hy).symm

theorem N_normal (hne : D1 δ γ ≠ ⊥) :
    stab δ ≤ Subgroup.normalizer ((Qv μ ⊓ Qv δ : Subgroup G) : Set G) := by
  have hU : Ub δ γ ≤ Subgroup.normalizer ((Qv μ ⊓ Qv δ : Subgroup G) : Set G) := by
    intro u hu
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hy' : y ∈ Ub δ γ ⊓ Qv δ := by rw [hs.U_inf_Qδ hne]; exact hy
    rw [← hs.U_inf_Qδ hne]
    exact ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hy'.1) (Subgroup.inv_mem _ hu),
      (Subgroup.mem_normalizer_iff.mp (stab_le_normQv δ hu.2) y).mp hy'.2⟩
  have hE : stab μ ⊓ stab δ ≤ Subgroup.normalizer ((Qv μ ⊓ Qv δ : Subgroup G) : Set G) := by
    intro e he
    refine mem_normalizer_of_conj_mem fun y hy => ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (stab_le_normQv μ he.1) y).mp hy.1
    · exact (Subgroup.mem_normalizer_iff.mp (stab_le_normQv δ he.2) y).mp hy.2
  exact hs.stab_le_sup.trans (sup_le (L_le_U.trans hU) hE)

theorem exists_q : ∃ q ∈ Qv δ, q ∉ Qv μ := by
  by_contra hcon
  push Not at hcon
  have hle : Qv δ ≤ Qv μ := fun q hq => hcon q hq
  have h1 : stab μ ⊓ stab δ = Qv μ := by rw [← hs.prod, sup_eq_left.mpr hle]
  have h2 := hs.idx
  rw [h1, Subgroup.relIndex_self] at h2
  omega

theorem coset {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) {r : G} (hr : r ∈ Qv δ) :
    r ∈ Qv μ ⊓ Qv δ ∨ r * q⁻¹ ∈ Qv μ ⊓ Qv δ := by
  by_cases hrQ : r ∈ Qv μ
  · exact Or.inl ⟨hrQ, hr⟩
  · exact Or.inr ⟨F53B3.O1.mul_inv_mem_of_relIndex_two hs.idx (hs.Qδ_le_E hr) (hs.Qδ_le_E hq)
      hrQ hqQ, Subgroup.mul_mem _ hr (Subgroup.inv_mem _ hq)⟩

theorem comm_Q (hne : D1 δ γ ≠ ⊥) {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) {g r : G}
    (hg : g ∈ stab δ) (hr : r ∈ Qv δ) : g * r * g⁻¹ * r⁻¹ ∈ Qv μ ⊓ Qv δ := by
  have hnorm := hs.N_normal hne hg
  have hr' : g * r * g⁻¹ ∈ Qv δ :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normQv δ hg) r).mp hr
  by_cases hrN : r ∈ Qv μ ⊓ Qv δ
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hnorm r).mp hrN) (inv_mem hrN)
  · have h1 : r * q⁻¹ ∈ Qv μ ⊓ Qv δ := (hs.coset hq hqQ hr).resolve_left hrN
    have hr'N : g * r * g⁻¹ ∉ Qv μ ⊓ Qv δ := fun h =>
      hrN ((Subgroup.mem_normalizer_iff.mp hnorm r).mpr h)
    have h2 : g * r * g⁻¹ * q⁻¹ ∈ Qv μ ⊓ Qv δ := (hs.coset hq hqQ hr').resolve_left hr'N
    have e : g * r * g⁻¹ * r⁻¹ = (g * r * g⁻¹ * q⁻¹) * (r * q⁻¹)⁻¹ := by group
    rw [e]
    exact mul_mem h2 (inv_mem h1)

theorem U_normal (hne : D1 δ γ ≠ ⊥) : stab δ ≤ Subgroup.normalizer (Ub δ γ : Set G) := by
  obtain ⟨q, hq, hqQ⟩ := hs.exists_q
  have hQδ : Qv δ ≤ Subgroup.normalizer (Ub δ γ : Set G) := by
    intro r hr
    refine mem_normalizer_of_conj_mem fun u hu => ?_
    have hc := hs.comm_Q hne hq hqQ hu.2 hr
    have hcU : u * r * u⁻¹ * r⁻¹ ∈ Ub δ γ := hs.Qμ_le_U hc.1
    have e : r * u * r⁻¹ = (u * r * u⁻¹ * r⁻¹)⁻¹ * u := by group
    rw [e]
    exact mul_mem (inv_mem hcU) hu
  have hsup : stab δ ≤ Ub δ γ ⊔ Qv δ := by
    refine hs.stab_le_sup.trans (sup_le (le_sup_of_le_left L_le_U) ?_)
    rw [← hs.prod]
    exact sup_le (le_sup_of_le_left hs.Qμ_le_U) le_sup_right
  exact hsup.trans (sup_le (fun u hu => Subgroup.le_normalizer hu) hQδ)

theorem sq_mem {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) :
    q * q ∈ Qv μ ⊓ Qv δ := by
  rcases hs.coset hq hqQ (Subgroup.mul_mem _ hq hq) with h | h
  · exact h
  · exfalso
    have : q * q * q⁻¹ = q := by group
    rw [this] at h
    exact hqQ h.1

theorem Yb_le_Zμ {q : G} (hq : q ∈ Qv δ) : Yb δ γ q ≤ Zv μ := by
  refine sup_le hs.D1_le_Zμ ?_
  intro y hy
  obtain ⟨x, hx, rfl⟩ := mem_map_conj.mp hy
  have hqμ : q ∈ stab μ := (hs.Qδ_le_E hq).1
  exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hs.hA μ hqμ) x).mp
    (hs.D1_le_Zμ hx)

theorem U_comm_Y (hne : D1 δ γ ≠ ⊥) {q : G} (hq : q ∈ Qv δ) {u : G} (hu : u ∈ Ub δ γ) {y : G}
    (hy : y ∈ Yb δ γ q) : u * y = y * u := by
  have hle : Yb δ γ q ≤ Subgroup.centralizer (Ub δ γ : Set G) := by
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.mp hu.1 x hx).symm
    · obtain ⟨x, hx, rfl⟩ := mem_map_conj.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hqs : q⁻¹ ∈ stab δ := Subgroup.inv_mem _ (pCoreOf_le 2 _ hq)
      have hw : q⁻¹ * u * q⁻¹⁻¹ ∈ Ub δ γ :=
        (Subgroup.mem_normalizer_iff.mp (hs.U_normal hne hqs) u).mp hu
      have hc := Subgroup.mem_centralizer_iff.mp hw.1 x hx
      calc u * (q * x * q⁻¹) = q * ((q⁻¹ * u * q⁻¹⁻¹) * x) * q⁻¹ := by group
        _ = q * (x * (q⁻¹ * u * q⁻¹⁻¹)) * q⁻¹ := by rw [← hc]
        _ = (q * x * q⁻¹) * u := by group
  exact Subgroup.mem_centralizer_iff.mp (hle hy) u hu

theorem q_norm_Y {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) :
    q ∈ Subgroup.normalizer (Yb δ γ q : Set G) := by
  refine mem_normalizer_of_conj_mem (conj_mem_sup_of q (fun a ha => ?_) (fun b hb => ?_))
  · exact conj_mem_Yb ha
  · obtain ⟨x, hx, rfl⟩ := mem_map_conj.mp hb
    have hq2 : q * q ∈ Ub δ γ := hs.Qμ_le_U (hs.sq_mem hq hqQ).1
    have hc := Subgroup.mem_centralizer_iff.mp hq2.1 x hx
    have e : q * (q * x * q⁻¹) * q⁻¹ = x := by
      calc q * (q * x * q⁻¹) * q⁻¹ = (q * q) * x * (q * q)⁻¹ := by group
        _ = (x * (q * q)) * (q * q)⁻¹ := by rw [hc]
        _ = x := by group
    rw [e]
    exact mem_Yb_left hx

theorem Qδ_norm_Y (hne : D1 δ γ ≠ ⊥) {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) :
    Qv δ ≤ Subgroup.normalizer (Yb δ γ q : Set G) := by
  intro r hr
  rcases hs.coset hq hqQ hr with h | h
  · exact mem_normalizer_of_comm fun y hy => hs.U_comm_Y hne hq (hs.Qμ_le_U h.1) hy
  · obtain ⟨n, hn, rfl⟩ : ∃ n ∈ Qv μ ⊓ Qv δ, r = n * q := ⟨r * q⁻¹, h, by group⟩
    refine mem_normalizer_of_conj_mem fun y hy => ?_
    have hz : q * y * q⁻¹ ∈ Yb δ γ q :=
      (Subgroup.mem_normalizer_iff.mp (hs.q_norm_Y hq hqQ) y).mp hy
    have hc := hs.U_comm_Y hne hq (hs.Qμ_le_U hn.1) hz
    have e : n * q * y * (n * q)⁻¹ = q * y * q⁻¹ := by
      calc n * q * y * (n * q)⁻¹ = n * (q * y * q⁻¹) * n⁻¹ := by group
        _ = q * y * q⁻¹ := by rw [hc]; group
    rw [e]
    exact hz

theorem E_norm_Y (hne : D1 δ γ ≠ ⊥) {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) :
    stab μ ⊓ stab δ ≤ Subgroup.normalizer (Yb δ γ q : Set G) := by
  rw [← hs.prod]
  exact sup_le (fun u hu => mem_normalizer_of_comm fun y hy =>
    hs.U_comm_Y hne hq (hs.Qμ_le_U hu) hy) (hs.Qδ_norm_Y hne hq hqQ)

theorem stabδ_norm_Y (hne : D1 δ γ ≠ ⊥) {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) :
    stab δ ≤ Subgroup.normalizer (Yb δ γ q : Set G) := by
  refine hs.stab_le_sup.trans (sup_le ((L_le_U (γ := γ)).trans ?_) (hs.E_norm_Y hne hq hqQ))
  intro u hu
  exact mem_normalizer_of_comm fun y hy => hs.U_comm_Y hne hq hu hy

theorem edgeγ_norm_Y {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) :
    stab μ ⊓ stab γ ≤ Subgroup.normalizer (Yb δ γ q : Set G) := by
  intro s hs'
  refine mem_normalizer_of_conj_mem (conj_mem_sup_of s (fun a ha => ?_) (fun b hb => ?_))
  · have hc := hs.stabγ_comm hs'.2 (D1_le_Zγ ha)
    have e : s * a * s⁻¹ = a := by rw [← hc]; group
    rw [e]
    exact mem_Yb_left ha
  · obtain ⟨x, hx, rfl⟩ := mem_map_conj.mp hb
    have hxZ : x ∈ Zv μ := hs.D1_le_Zμ hx
    have hqμ : q ∈ stab μ := (hs.Qδ_le_E hq).1
    have hbZ : q * x * q⁻¹ ∈ Zv μ :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hs.hA μ hqμ) x).mp hxZ
    by_cases hsQ : s ∈ Qv μ
    · have hc := hs.Qμ_comm hsQ hbZ
      have e : s * (q * x * q⁻¹) * s⁻¹ = q * x * q⁻¹ := by rw [← hc]; group
      rw [e]
      exact conj_mem_Yb hx
    · have hq2 : q ^ 2 ∈ Qv μ := by rw [pow_two]; exact (hs.sq_mem hq hqQ).1
      have hs2 : s ^ 2 ∈ Qv μ := by
        by_contra h
        have h1 := F53B3.O1.mul_inv_mem_of_relIndex_two hs.idxγ ((stab μ ⊓ stab γ).pow_mem hs' 2)
          hs' h hsQ
        have e : s ^ 2 * s⁻¹ = s := by group
        rw [e] at h1
        exact hsQ h1
      have hqs : q * s⁻¹ ∉ Qv μ := by
        intro hk
        have hsE : s ∈ stab μ ⊓ stab δ := by
          have e : s = (q * s⁻¹)⁻¹ * q := by group
          rw [e]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hs.Qμ_le_E hk)) (hs.Qδ_le_E hq)
        exact hsQ (hs.T.mem_Qv_of_fix hs.hA (g := ⟨s, CosetGeom.stab_le μ hs'.1⟩) hs'.1
          (smul_eq_of_mem_stab hsE.2) (smul_eq_of_mem_stab hs'.2))
      obtain ⟨hd1, hd3⟩ := three_cycle hs.hA hs.vμ hqμ hs'.1 hqQ hsQ hq2 hs2 hqs
      have hrel := rel3 hs.hA hs.vμ hs.nδ hs.zδ (Subgroup.mul_mem _ hqμ hs'.1) hd1 hd3 hxZ
      have hsx : s * x * s⁻¹ = x := by rw [← hs.stabγ_comm hs'.2 (D1_le_Zγ hx)]; group
      have h1 : (q * s) * x * (q * s)⁻¹ = q * x * q⁻¹ := by
        calc (q * s) * x * (q * s)⁻¹ = q * (s * x * s⁻¹) * q⁻¹ := by group
          _ = q * x * q⁻¹ := by rw [hsx]
      have h2 : (q * s) ^ 2 * x * ((q * s) ^ 2)⁻¹ = q * (s * (q * x * q⁻¹) * s⁻¹) * q⁻¹ := by
        rw [pow_two, mul_inv_rev]
        calc q * s * (q * s) * x * ((q * s)⁻¹ * (q * s)⁻¹)
            = (q * s) * ((q * s) * x * (q * s)⁻¹) * (q * s)⁻¹ := by group
          _ = (q * s) * (q * x * q⁻¹) * (q * s)⁻¹ := by rw [h1]
          _ = q * (s * (q * x * q⁻¹) * s⁻¹) * q⁻¹ := by group
      rw [h1, h2] at hrel
      have h3 := eq_inv_of_mul_eq_one_right hrel
      have h4 : s * (q * x * q⁻¹) * s⁻¹ = q⁻¹ * (x * (q * x * q⁻¹))⁻¹ * q⁻¹⁻¹ := by
        rw [← h3]; group
      have hw : (x * (q * x * q⁻¹))⁻¹ ∈ Yb δ γ q :=
        Subgroup.inv_mem _ (Subgroup.mul_mem _ (mem_Yb_left hx) (conj_mem_Yb hx))
      rw [h4]
      exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hs.q_norm_Y hq hqQ)) _).mp hw

theorem stabμ_norm_Y (hne : D1 δ γ ≠ ⊥) {q : G} (hq : q ∈ Qv δ) (hqQ : q ∉ Qv μ) :
    stab μ ≤ Subgroup.normalizer (Yb δ γ q : Set G) := by
  have hsup := sup_edges_eq_stab hs.hA hs.vμ hs.nδ hs.nγ hs.T.hab
  intro g hg
  rw [← hsup] at hg
  exact sup_le (hs.E_norm_Y hne hq hqQ) (hs.edgeγ_norm_Y hq hqQ) hg

theorem D1_eq_bot : D1 δ γ = ⊥ := by
  by_contra hne
  obtain ⟨q, hq, hqQ⟩ := hs.exists_q
  have hU : Yb δ γ q ≤ stab μ ⊓ stab δ :=
    (hs.Yb_le_Zμ hq).trans ((Zv_le_Qv hs.hA μ).trans hs.Qμ_le_E)
  have hY : Yb δ γ q = ⊥ := eq_bot_of_normalizes_both hs.hA hs.adj hU
    (hs.stabμ_norm_Y hne hq hqQ) (hs.stabδ_norm_Y hne hq hqQ)
  exact hne (eq_bot_iff.mpr (fun x hx => hY ▸ mem_Yb_left hx))

end DSit

theorem Cb_inf_Zv_eq (hG : Glob H M S) {δ μ : Geo H M} (hδ : vtype δ = false)
    (hμ : μ ∈ nbrs δ) : Cb δ ⊓ Zv μ = Zv δ := by
  have hvμ : vtype μ = true := by
    have h := vtype_ne_of_adj (show (graph (H ⊔ M) H M).Adj δ μ from hμ)
    rw [hδ] at h
    cases hv : vtype μ
    · exact absurd hv.symm h
    · rfl
  obtain ⟨γ, γ', T⟩ := exists_tri hG.amalg hvμ (nbrs_symm hμ)
  have hs : DSit H M S δ μ γ γ' := ⟨hG, hδ, T⟩
  refine le_antisymm ?_ (le_inf (Zv_le_Cb hG hδ) hs.Zδμ)
  rintro x ⟨hxC, hxZ⟩
  rw [← hs.Zsup.1] at hxZ
  obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup (fun a ha b hb =>
    EmptyFaithful.Stellmacher.OrdinaryProofs.comm_Zv_comm hG.amalg μ a (hs.Zδμ ha) b
      (hs.Zγμ hb)) hxZ
  have hbC : b ∈ D1 δ γ := by
    refine ⟨?_, hb⟩
    have e : b = a⁻¹ * (a * b) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Zv_le_Cb hG hδ ha)) hxC
  rw [hs.D1_eq_bot, Subgroup.mem_bot] at hbC
  rw [hbC, mul_one]
  exact ha

end S34

end F53.Stellmacher

end CFSG.Quasithin
