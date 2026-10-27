module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModG
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseM17Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModC2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

structure W17Hyp (α : Geo H M) : Prop where
  Wn_le_Qv : Wn α ≤ Qv α
  Vn_le_Wn : ∀ δ ∈ nbrs α, Vn δ ≤ Wn α
  comm_le : ⁅Wn α, Wn α⁆ ≤ Zv α
  sq_mem : ∀ x ∈ Wn α, x ^ 2 ∈ Zv α
  stab_le_normalizer : stab α ≤ Subgroup.normalizer (Wn α : Set G)

structure S17Hyp (α δ : Geo H M) (E F : Subgroup G) : Prop where
  hδ : δ ∈ nbrs α
  hE : stab α ≤ Subgroup.normalizer (E : Set G)
  hF : stab α ≤ Subgroup.normalizer (F : Set G)
  hZE : Zv α ≤ E
  hEF : E ≤ F
  hFW : F ≤ Wn α
  hC : ∀ w ∈ Wn α, (∀ g ∈ stab α, g * w * g⁻¹ * w⁻¹ ∈ E) → w ∈ E
  hVF : Vn δ ⊔ F = Wn α

variable {α δ : Geo H M} {E F : Subgroup G}

omit [Finite G] in
theorem W17Hyp.Wn_le_stab (hW : W17Hyp α) : Wn α ≤ stab α :=
  hW.Wn_le_Qv.trans (pCoreOf_le 2 _)

omit [Finite G] in
theorem W17Hyp.Vn_le_stab (hW : W17Hyp α) (hδ : δ ∈ nbrs α) : Vn δ ≤ stab α :=
  (hW.Vn_le_Wn δ hδ).trans hW.Wn_le_stab

omit [Finite G] in
theorem S17Hyp.isSec (hW : W17Hyp α) (h : S17Hyp α δ E F) : IsSec (stab α) E (Wn α) where
  le := h.hEF.trans h.hFW
  normN := hW.stab_le_normalizer
  normL := h.hE
  comm := fun _ hx _ hy => h.hZE (hW.comm_le (Subgroup.commutator_mem_commutator hx hy))
  sq := fun x hx => h.hZE (hW.sq_mem x hx)

omit [Finite G] in
theorem S17Hyp.decomp (hW : W17Hyp α) (h : S17Hyp α δ E F) {w : G} (hw : w ∈ Wn α) :
    ∃ f ∈ F, ∃ v ∈ Vn δ, w = f * v := by
  have hn : Vn δ ≤ Subgroup.normalizer (F : Set G) := (hW.Vn_le_stab h.hδ).trans h.hF
  rw [← h.hVF, sup_comm] at hw
  exact (F1.mem_sup_iff_exists_mul_of_normalizes hn).mp hw

section Sec

variable {X L N : Subgroup G}

omit [Finite G] in
theorem sec_fix_iff (hs : IsSec X L N) (x : ↥X) (w : ↥N) :
    hs.conjHom x (hs.proj w) = hs.proj w ↔ (x : G) * w * (x : G)⁻¹ * (w : G)⁻¹ ∈ L := by
  rw [IsSec.conjHom_mk, ← mul_inv_eq_one, ← map_inv, ← map_mul, hs.proj_eq_one_iff]
  simp [IsSec.conjN]

omit [Finite G] in
theorem sec_mem_tilde_iff (hs : IsSec X L N) {K : Subgroup G} (hLK : L ≤ K) (y : ↥N) :
    hs.proj y ∈ (K.subgroupOf N).map hs.proj ↔ (y : G) ∈ K := by
  constructor
  · rintro ⟨z, hz, hzy⟩
    have h1 := (hs.proj_eq_proj_iff z y).mp hzy
    have hz' : (z : G) ∈ K := hz
    have e : (y : G) = (z : G) * ((z : G)⁻¹ * y) := by group
    rw [e]
    exact K.mul_mem hz' (hLK h1)
  · intro hy
    exact ⟨y, hy, rfl⟩

omit [Finite G] in
theorem sec_ker_proj (hs : IsSec X L N) : hs.proj.ker = L.subgroupOf N := by
  have := hs.normal_subgroupOf
  exact QuotientGroup.ker_mk' _

omit [Finite G] in
theorem sec_card_tilde (hs : IsSec X L N) {K : Subgroup G} (hKN : K ≤ N) :
    Nat.card ((K.subgroupOf N).map hs.proj) = L.relIndex K := by
  rw [← Subgroup.relIndex_ker, sec_ker_proj hs, Subgroup.relIndex_subgroupOf hKN]

omit [Finite G] in
theorem sec_index_tilde (hs : IsSec X L N) {K : Subgroup G} (hLK : L ≤ K) :
    ((K.subgroupOf N).map hs.proj).index = K.relIndex N := by
  have hle : hs.proj.ker ≤ K.subgroupOf N := by
    rw [sec_ker_proj hs]
    exact fun x hx => hLK hx
  rw [Subgroup.index_map, sup_eq_left.mpr hle, MonoidHom.range_eq_top.mpr hs.proj_surjective,
    Subgroup.index_top, mul_one]
  rfl

end Sec

namespace Sit43

theorem comm_Qst_Vn_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : δ ∈ nbrs α) {x v : G} (hx : x ∈ Qst δ) (hv : v ∈ Vn δ) :
    x * v * x⁻¹ * v⁻¹ ∈ Zv α := by
  have hδv : vtype δ = true := vtype_true_of_adj hs.vα hδ
  have h1 : ⁅v, x⁆ ∈ Zv α := Yv_le_Zv (nbrs_symm hδ) (hs.comm_Vn_Qst hA h26 hδv (nbrs_symm hδ) ▸
    Subgroup.commutator_mem_commutator hv hx)
  have h2 := (Zv α).inv_mem h1
  have e : ⁅v, x⁆⁻¹ = x * v * x⁻¹ * v⁻¹ := by simp only [commutatorElement_def]; group
  rwa [e] at h2

theorem relIndex_Qst_le_two (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : δ ∈ nbrs α) {P : Subgroup G} (hP : P ≤ Qv α) : (Qst δ).relIndex P ≤ 2 := by
  have hQ : Qv α ⊓ Qv δ ≤ Qst δ := Qv_inf_Qv_le_Qst hA (nbrs_symm hδ)
  have h1 : (Qst δ).relIndex P ∣ (Qv α ⊓ Qv δ).relIndex P :=
    Subgroup.relIndex_dvd_of_le_left P hQ
  have h2 := Subgroup.relIndex_inf_mul_relIndex (Qv δ) (Qv α) P
  rw [inf_eq_right.mpr hP, Subgroup.relIndex_eq_one.mpr hP, mul_one, inf_comm] at h2
  have h3 : (Qv δ).relIndex (Qv α) = 2 := hs.relIndex_Qv_Qv hA h26 hs.vα hδ
  have h4 : (Qv δ).relIndex P ≤ 2 := by
    rw [← h3]
    exact Subgroup.relIndex_le_of_le_right hP (by rw [h3]; norm_num)
  rw [h2] at h4
  have hpos : 0 < (Qv α ⊓ Qv δ).relIndex P := Nat.pos_of_ne_zero (by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite)
  exact (Nat.le_of_dvd hpos h1).trans h4

theorem mem_of_commutator_Lres {M : Model 5} (hM : IsModelSec M (stab α) E F)
    (hfix : ∀ w : M.W, (∀ σ ∈ alternatingGroup (Fin 5), M.act σ w = w) → w = 1)
    (hE : stab α ≤ Subgroup.normalizer (E : Set G)) (hFst : F ≤ stab α) {f : G} (hf : f ∈ F)
    (hfl : ∀ l ∈ Lres α, l * f * l⁻¹ * f⁻¹ ∈ E) : f ∈ E := by
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := hM
  obtain ⟨u, hu⟩ := hsd.surj (QuotientGroup.mk (⟨f, hf⟩ : ↥F))
  have hu1 : u = 1 := by
    apply hfix u
    intro σ hσ
    rw [← map_oTwoRes_eq_alt hθs] at hσ
    obtain ⟨l, hl, rfl⟩ := hσ
    have hl' : (l : G) ∈ oTwoRes (stab α) := hl
    obtain ⟨hlx, h1⟩ := hsd.equiv l u ⟨f, hf⟩ hu
    apply hsd.inj
    rw [h1, hu, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc := E.inv_mem (hfl l hl')
    have hconj := (Subgroup.mem_normalizer_iff.mp (hE (hFst (F.inv_mem hf))) _).mp hc
    have e : ((⟨(l : G) * f * (l : G)⁻¹, hlx⟩ : ↥F)⁻¹ * ⟨f, hf⟩ : ↥F).val =
        f⁻¹ * ((l : G) * f * (l : G)⁻¹ * f⁻¹)⁻¹ * f⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact hconj
  rw [hu1, map_one] at hu
  exact (QuotientGroup.eq_one_iff (N := E.subgroupOf F) (⟨f, hf⟩ : ↥F)).mp hu.symm

theorem exists_Qst_of_S5That (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hδ : δ ∈ nbrs α) (D : Dict5 (stab α) (stab α ⊓ stab δ) (Zv α)) {τ : Perm (Fin 5)}
    (hτ : τ ∈ S5That) : ∃ k ∈ Qst δ, ∃ hk : k ∈ stab α, D.ψ ⟨k, hk⟩ = τ := by
  have hδv : vtype δ = true := vtype_true_of_adj hs.vα hδ
  have hαδ : α ∈ nbrs δ := nbrs_symm hδ
  have hYc := hs.Yv_eq_comm_comm hA h26 hδv hαδ
  have hSyl : τ ∈ D.bar (stab α ⊓ stab δ) := by
    rw [D.bar_S]; exact S5That_le_S5Syl hτ
  obtain ⟨x, hxS, hxψ⟩ := (D.mem_bar_iff _).mp hSyl
  have hxC : (x : G) ∈ (stab α ⊓ stab δ) ⊓ Subgroup.centralizer (Yv δ : Set G) := by
    rw [hYc]
    exact (D.mem_centralizer_Y_iff x).mpr (by rw [hxψ]; exact hτ)
  rw [← hs.Qv_sup_Qst hA h26 hδv hαδ] at hxC
  obtain ⟨q, hq, a, ha, hqa⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    (((inf_le_left : Qst δ ≤ Qv δ).trans (Qv_le_stab_of_mem_nbrs hA hαδ)).trans
      (le_normalizer_pCoreOf 2 (stab α)))).mp hxC
  have hqX : q ∈ stab α := pCoreOf_le 2 _ hq
  have haX : a ∈ stab α := inf_le_left.trans (Qv_le_stab_of_mem_nbrs hA hαδ) ha
  refine ⟨a, ha, haX, ?_⟩
  have h1 : D.ψ ⟨q, hqX⟩ = 1 := (D.ker_iff _).mpr hq
  have h2 : x = ⟨q, hqX⟩ * ⟨a, haX⟩ := Subtype.ext hqa
  rw [← hxψ, h2, map_mul, h1, one_mul]

theorem commutator_Lres_mem (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hW : W17Hyp α) (h : S17Hyp α δ E F) :
    ∀ l ∈ Lres α, ∀ w ∈ Wn α, l * w * l⁻¹ * w⁻¹ ∈ F := by
  obtain ⟨D⟩ := hs.exists_dict hA h.hδ
  have hδv : vtype δ = true := vtype_true_of_adj hs.vα h.hδ
  have hαδ : α ∈ nbrs δ := nbrs_symm h.hδ
  have hQs : Qst δ ≤ stab α := inf_le_left.trans (Qv_le_stab_of_mem_nbrs hA hαδ)
  have hτ : (Equiv.swap 0 2 : Perm (Fin 5)) ∈ S5That := Subgroup.subset_closure (by simp)
  obtain ⟨k, hk, hkX, hψ⟩ := hs.exists_Qst_of_S5That hA h26 h.hδ D hτ
  obtain ⟨C, hC, hCX, hCn⟩ := exists_centralizer_quotient h.hF hW.stab_le_normalizer
  have hkC : k ∈ C := (hC k).mpr ⟨hkX, fun n hn => by
    obtain ⟨f, hf, v, hv, rfl⟩ := h.decomp hW hn
    have hcv : ⁅v, k⁆ ∈ F := h.hEF (h.hZE (Yv_le_Zv hαδ (hs.comm_Vn_Qst hA h26 hδv hαδ ▸
      Subgroup.commutator_mem_commutator hv hk)))
    have e : ⁅f * v, k⁆ = f * ⁅v, k⁆ * f⁻¹ * (f * (k * f⁻¹ * k⁻¹)) := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h1 : k * f⁻¹ * k⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp (h.hF hkX) _).mp (F.inv_mem hf)
    exact F.mul_mem (F.mul_mem (F.mul_mem hf hcv) (F.inv_mem hf)) (F.mul_mem hf h1)⟩
  have hLC : oTwoRes (stab α) ≤ C := D.oTwoRes_le_of_swap hCn hkC hkX hψ
  intro l hl w hw
  have h1 := F.inv_mem (((hC l).mp (hLC hl)).2 w hw)
  have e : ⁅w, l⁆⁻¹ = l * w * l⁻¹ * w⁻¹ := by simp only [commutatorElement_def]; group
  rwa [e] at h1

theorem S17_core (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) (hW : W17Hyp α)
    (h : S17Hyp α δ E F) (hchief : IsChiefStep (stab α) (Wn α) E F) {Mo : Model 5}
    (hM : IsModelSec Mo (stab α) E F) (hcs : cSecIn (stab α) E F = Qv α)
    (hfix : ∀ w : Mo.W, (∀ σ ∈ alternatingGroup (Fin 5), Mo.act σ w = w) → w = 1) :
    (∀ q ∈ Qv α, ∀ w ∈ Wn α, q * w * q⁻¹ * w⁻¹ ∈ E) ∧
    ∃ (W : Model 5) (j : Mo.W →* W.W) (B : Subgroup W.W),
      Function.Injective j ∧ (∀ (σ : Perm (Fin 5)) (u : Mo.W), j (Mo.act σ u) = W.act σ (j u)) ∧
      (∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ j.range) ∧
      (∀ w : W.W, (∀ σ ∈ alternatingGroup (Fin 5), W.act σ w = w) → w = 1) ∧
      (∀ σ ∈ S5That, ∀ b ∈ B, W.act σ b = b) ∧ B ⊔ j.range = ⊤ ∧
      j.range.relIndex ⊤ = F.relIndex (Wn α) ∧ Nat.card B = E.relIndex (Vn δ ⊔ E) ∧
      E.relIndex ((Vn δ ⊔ E) ⊓ F) ≤ Nat.card ↥(B ⊓ j.range) ∧ (j.range = ⊤ → F = Wn α) := by
  have hsec := h.isSec hW
  have hfinA : Finite hsec.W := by
    have := hsec.normal_subgroupOf
    exact (inferInstance : Finite (↥(Wn α) ⧸ E.subgroupOf (Wn α)))
  have hA2 : IsPGroup 2 hsec.W := by
    have h2 : IsPGroup 2 ↥(Wn α) := (pCoreOf_isPGroup (r := 2) (stab α)).to_le hW.Wn_le_Qv
    exact h2.of_surjective hsec.proj hsec.proj_surjective
  let Ft : Subgroup hsec.W := (F.subgroupOf (Wn α)).map hsec.proj
  let Bt : Subgroup hsec.W := ((Vn δ ⊔ E).subgroupOf (Wn α)).map hsec.proj
  let L' : Subgroup ↥(stab α) := (Lres α).subgroupOf (stab α)
  let Q' : Subgroup ↥(stab α) := (Qv α).subgroupOf (stab α)
  let R' : Subgroup ↥(stab α) := (Qst δ).subgroupOf (stab α)
  have hFt : ∀ y : ↥(Wn α), hsec.proj y ∈ Ft ↔ (y : G) ∈ F := sec_mem_tilde_iff hsec h.hEF
  have hEVE : E ≤ Vn δ ⊔ E := le_sup_right
  have hBt : ∀ y : ↥(Wn α), hsec.proj y ∈ Bt ↔ (y : G) ∈ Vn δ ⊔ E := sec_mem_tilde_iff hsec hEVE
  have hVnE : Vn δ ≤ Subgroup.normalizer (E : Set G) := (hW.Vn_le_stab h.hδ).trans h.hE
  have hLn : ∀ x : ↥(stab α), ∀ l ∈ L', x * l * x⁻¹ ∈ L' := fun x l hl =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (stab α) x.2) (l : G)).mp hl
  have hQn : ∀ x : ↥(stab α), ∀ q ∈ Q', x * q * x⁻¹ ∈ Q' := fun x q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab α) x.2) (q : G)).mp hq
  have hLF : ∀ l ∈ L', ∀ a : hsec.W, hsec.conjHom l a * a⁻¹ ∈ Ft := by
    intro l hl a
    obtain ⟨w, rfl⟩ := hsec.proj_surjective a
    have e : hsec.conjHom l (hsec.proj w) * (hsec.proj w)⁻¹ =
        hsec.proj (hsec.conjN l w * w⁻¹) := by
      rw [IsSec.conjHom_mk, map_mul, map_inv]
    rw [e, hFt]
    have h1 := hs.commutator_Lres_mem hA h26 hW h (l : G) hl (w : G) w.2
    simpa [IsSec.conjN] using h1
  have hQF : ∀ q ∈ Q', ∀ f ∈ Ft, hsec.conjHom q f = f := by
    intro q hq f hf
    obtain ⟨y, hy, rfl⟩ := hf
    rw [sec_fix_iff]
    exact commutator_pCoreOf_mem hW.Wn_le_Qv hchief q hq y hy
  have hR : ∀ r ∈ R', ∀ b ∈ Bt, hsec.conjHom r b = b := by
    intro r hr b hb
    obtain ⟨y, hy, rfl⟩ := hb
    rw [sec_fix_iff]
    have hy' : (y : G) ∈ E ⊔ Vn δ := by rw [sup_comm]; exact hy
    obtain ⟨e, he, v, hv, hyev⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hVnE).mp hy'
    have h1 := comm_Qst_Vn_mem hA h26 hs h.hδ (x := (r : G)) hr hv
    have hre : (r : G) * e * (r : G)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (h.hE r.2) e).mp he
    rw [hyev]
    have e2 : (r : G) * (e * v) * (r : G)⁻¹ * (e * v)⁻¹ =
        ((r : G) * e * (r : G)⁻¹) * ((r : G) * v * (r : G)⁻¹ * v⁻¹) * e⁻¹ := by group
    rw [e2]
    exact E.mul_mem (E.mul_mem hre (h.hZE h1)) (E.inv_mem he)
  have hidx : R'.relIndex (L' ⊓ Q') ≤ 2 := by
    have e : L' ⊓ Q' = (Lres α ⊓ Qv α).subgroupOf (stab α) := Subgroup.ext fun _ => Iff.rfl
    have hKX : Lres α ⊓ Qv α ≤ stab α := inf_le_right.trans (pCoreOf_le 2 _)
    rw [e, Subgroup.relIndex_subgroupOf hKX]
    exact relIndex_Qst_le_two hA h26 hs h.hδ inf_le_right
  have hF1 : ∀ f ∈ Ft, (∀ l ∈ L', hsec.conjHom l f = f) → f = 1 := by
    intro f hf hfl
    obtain ⟨y, hy, rfl⟩ := hf
    rw [hsec.proj_eq_one_iff]
    refine mem_of_commutator_Lres hM hfix h.hE (h.hFW.trans hW.Wn_le_stab) hy ?_
    intro l hl
    have hlX : l ∈ stab α := oTwoRes_le _ hl
    exact (sec_fix_iff hsec ⟨l, hlX⟩ y).mp (hfl ⟨l, hlX⟩ hl)
  have hC : ∀ a : hsec.W, (∀ x : ↥(stab α), hsec.conjHom x a = a) → a = 1 := by
    intro a ha
    obtain ⟨w, rfl⟩ := hsec.proj_surjective a
    rw [hsec.proj_eq_one_iff]
    exact h.hC w w.2 fun g hg => (sec_fix_iff hsec ⟨g, hg⟩ w).mp (ha ⟨g, hg⟩)
  have hAB : ∀ a : hsec.W, ∃ b ∈ Bt, ∃ f ∈ Ft, a = b * f := by
    intro a
    obtain ⟨w, rfl⟩ := hsec.proj_surjective a
    obtain ⟨f, hf, v, hv, hwfv⟩ := h.decomp hW w.2
    have hvW : v ∈ Wn α := hW.Vn_le_Wn δ h.hδ hv
    have hfW : f ∈ Wn α := h.hFW hf
    refine ⟨hsec.proj ⟨v, hvW⟩, (hBt _).mpr ((le_sup_left : Vn δ ≤ Vn δ ⊔ E) hv),
      hsec.proj ⟨f, hfW⟩, (hFt _).mpr hf, ?_⟩
    have hw : w = ⟨f, hfW⟩ * ⟨v, hvW⟩ := Subtype.ext hwfv
    rw [hw, map_mul, mul_comm]
  obtain ⟨hSX, hSp, -⟩ := sylow_stab_inf_left hA h.hδ
  have hcov : ∀ x : ↥(stab α), ∃ l ∈ L', ∃ p : ↥(stab α ⊓ stab δ),
      x = l * Subgroup.inclusion inf_le_left p := by
    intro x
    have hx : (x : G) ∈ oTwoRes (stab α) ⊔ (stab α ⊓ stab δ) :=
      le_oTwoRes_sup_of_isSylowTwoOf (sylow_stab_inf_left hA h.hδ) x.2
    obtain ⟨a, ha, b, hb, hxab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (hSX.trans (le_normalizer_oTwoRes (stab α)))).mp hx
    exact ⟨⟨a, oTwoRes_le _ ha⟩, ha, ⟨b, hb⟩, Subtype.ext hxab⟩
  have hCL := eq_one_of_fixed_of_cover (ρ := hsec.conjHom) hA2 (L := L') hLn hSp
    (Subgroup.inclusion inf_le_left) hcov hC
  have hLB := fixed_on_of_hom (ρ := hsec.conjHom) (F := Ft) (B := Bt) (L := L') (P := L' ⊓ Q')
    (R := R') hLF inf_le_left (fun l hl t ht => ⟨hLn l t ht.1, hQn l t ht.2⟩)
    (fun t ht f hf => hQF t ht.2 f hf) hR hidx hF1
  have hQ := fixed_on_of_comm (ρ := hsec.conjHom) (F := Ft) (B := Bt) (L := L') (Q := Q')
    hLn hQn hLF hQF hLB hAB hCL
  have hQtriv : ∀ q ∈ Qv α, ∀ w ∈ Wn α, q * w * q⁻¹ * w⁻¹ ∈ E := fun q hq w hw =>
    (sec_fix_iff hsec ⟨q, pCoreOf_le 2 _ hq⟩ ⟨w, hw⟩).mp
      (hQ ⟨q, pCoreOf_le 2 _ hq⟩ hq (hsec.proj ⟨w, hw⟩))
  refine ⟨hQtriv, ?_⟩
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := hM
  have := hn
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ :=
    hsd.exists_normalized hθs hθk (sylow_stab_inf_left hA h.hδ)
  have hkΨ' : Ψ.ker = (Qv α).subgroupOf (stab α) := by rw [hkΨ, hcs]
  have hk : Ψ.ker ≤ (cSecIn (stab α) E (Wn α)).subgroupOf (stab α) := by
    intro x hx
    rw [hkΨ'] at hx
    exact Subgroup.subset_closure ⟨x.2, fun w hw => hQtriv x hx w hw⟩
  have hnormW := hsec.normal_subgroupOf
  let W : Model 5 := secModule hsec Ψ hΨs hk
  have hact : ∀ (k : ↥(stab α)) (a : W.W), W.act (Ψ k) a = hsec.conjHom k a := by
    intro k a
    obtain ⟨y, rfl⟩ := hsec.proj_surjective a
    exact secModule_act_proj hsec Ψ hΨs hk k y
  let g : ↥F ⧸ E.subgroupOf F →* hsec.W :=
    QuotientGroup.map (E.subgroupOf F) (E.subgroupOf (Wn α)) (Subgroup.inclusion h.hFW)
      (fun x hx => hx)
  have hgmk : ∀ f : ↥F, g (QuotientGroup.mk f) = hsec.proj (Subgroup.inclusion h.hFW f) :=
    fun f => QuotientGroup.map_mk _ _ _ _ f
  let j : Mo.W →* W.W := g.comp β'
  have hjmk : ∀ (u : Mo.W) (f : ↥F), β' u = QuotientGroup.mk f →
      j u = hsec.proj (Subgroup.inclusion h.hFW f) := by
    intro u f hu
    show g (β' u) = _
    rw [hu, hgmk]
  have hinj : Function.Injective j := by
    rw [injective_iff_map_eq_one]
    intro u hu
    obtain ⟨f, hf⟩ := QuotientGroup.mk_surjective (β' u)
    have h1 := hjmk u f hf.symm
    rw [hu] at h1
    have h2 : ((Subgroup.inclusion h.hFW f : ↥(Wn α)) : G) ∈ E :=
      (hsec.proj_eq_one_iff _).mp h1.symm
    have h3 : β' u = 1 := by
      rw [← hf]
      exact (QuotientGroup.eq_one_iff f).mpr h2
    exact hsd'.inj (h3.trans (map_one β').symm)
  have hequiv : ∀ (σ : Perm (Fin 5)) (u : Mo.W),
      j (Mo.act σ u) = W.act σ (j u) := by
    intro σ u
    obtain ⟨k, rfl⟩ := hΨs σ
    obtain ⟨f, hf⟩ := QuotientGroup.mk_surjective (β' u)
    obtain ⟨hkf, h1⟩ := hsd'.equiv k u f hf.symm
    rw [hjmk _ _ h1, hact, hjmk u f hf.symm]
    rfl
  have hrange : ∀ y : ↥(Wn α), hsec.proj y ∈ j.range ↔ (y : G) ∈ F := by
    intro y
    constructor
    · rintro ⟨u, hu⟩
      obtain ⟨f, hf⟩ := QuotientGroup.mk_surjective (β' u)
      rw [hjmk u f hf.symm] at hu
      have h1 : hsec.proj (Subgroup.inclusion h.hFW f) ∈ Ft := ⟨_, f.2, rfl⟩
      rw [hu] at h1
      exact (hFt y).mp h1
    · intro hy
      obtain ⟨u, hu⟩ := hsd'.surj (QuotientGroup.mk (⟨y, hy⟩ : ↥F))
      exact ⟨u, by rw [hjmk u ⟨y, hy⟩ hu]; rfl⟩
  have hA5 : ∀ σ ∈ alternatingGroup (Fin 5), ∀ w : W.W, W.act σ w * w⁻¹ ∈ j.range := by
    intro σ hσ w
    rw [← map_oTwoRes_eq_alt hΨs] at hσ
    obtain ⟨l, hl, rfl⟩ := hσ
    obtain ⟨y, rfl⟩ := hsec.proj_surjective w
    have e : hsec.conjHom l (hsec.proj y) * (hsec.proj y)⁻¹ =
        hsec.proj (hsec.conjN l y * y⁻¹) := by rw [IsSec.conjHom_mk, map_mul, map_inv]
    have e0 : W.act (Ψ l) (hsec.proj y) = hsec.conjHom l (hsec.proj y) := hact l _
    rw [e0]
    show hsec.conjHom l (hsec.proj y) * (hsec.proj y)⁻¹ ∈ j.range
    rw [e, hrange]
    simpa [IsSec.conjN] using hs.commutator_Lres_mem hA h26 hW h (l : G) hl (y : G) y.2
  have hCW : ∀ w : W.W, (∀ σ ∈ alternatingGroup (Fin 5), W.act σ w = w) → w = 1 := by
    intro w hw
    refine hCL w fun l hl => ?_
    rw [← hact]
    apply hw
    rw [← map_oTwoRes_eq_alt hΨs]
    exact ⟨l, hl, rfl⟩
  obtain ⟨D⟩ := hs.exists_dict hA h.hδ
  obtain ⟨ι, hι⟩ : ∃ ι : Perm (Fin 5) →* Perm (Fin 5), ∀ x : ↥(stab α), ι (D.ψ x) = Ψ x := by
    have hker : D.ψ.ker ≤ Ψ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, D.ker_iff] at hx
      rw [hkΨ']
      exact hx
    refine ⟨MonoidHom.liftOfRightInverse D.ψ (Function.surjInv D.surj)
      (Function.rightInverse_surjInv D.surj) ⟨Ψ, hker⟩, fun x => ?_⟩
    exact MonoidHom.liftOfRightInverse_comp_apply D.ψ (Function.surjInv D.surj)
      (Function.rightInverse_surjInv D.surj) ⟨Ψ, hker⟩ x
  have hιinj : Function.Injective ι := by
    rw [injective_iff_map_eq_one]
    intro σ hσ
    obtain ⟨x, rfl⟩ := D.surj σ
    rw [hι] at hσ
    have hx : x ∈ Ψ.ker := hσ
    rw [hkΨ'] at hx
    exact (D.ker_iff x).mpr hx
  have hD : ∀ σ ∈ S5Syl, ι σ ∈ S5Syl := by
    intro σ hσ
    rw [← D.bar_S] at hσ
    obtain ⟨x, hxS, rfl⟩ := (D.mem_bar_iff σ).mp hσ
    rw [hι, ← hPS]
    exact ⟨x, hxS, rfl⟩
  have hTfix : ∀ τ ∈ S5That, ∃ k : ↥(stab α), (k : G) ∈ Qst δ ∧ Ψ k = τ := by
    intro τ hτ
    obtain ⟨σ, hσT, rfl⟩ := exists_map_S5That hιinj hD hτ
    obtain ⟨k, hk', hkX, hψ⟩ := hs.exists_Qst_of_S5That hA h26 h.hδ D hσT
    exact ⟨⟨k, hkX⟩, hk', by rw [← hι, hψ]⟩
  have hWfin : (∀ σ ∈ S5That, ∀ b ∈ Bt, W.act σ b = b) := by
    intro σ hσ b hb
    obtain ⟨k, hkq, rfl⟩ := hTfix σ hσ
    exact (hact k b).trans (hR k hkq b hb)
  refine ⟨W, j, Bt, hinj, hequiv, hA5, hCW, hWfin, ?_, ?_, ?_, ?_, ?_⟩
  · refine eq_top_iff.mpr fun a _ => ?_
    obtain ⟨b, hb, f, hf, rfl⟩ := hAB a
    obtain ⟨y, hy, rfl⟩ := hf
    exact Subgroup.mul_mem_sup hb ((hrange y).mpr hy)
  · have e : j.range = Ft := by
      ext a
      obtain ⟨y, rfl⟩ := hsec.proj_surjective a
      exact (hrange y).trans (hFt y).symm
    rw [Subgroup.relIndex_top_right]
    exact (congrArg Subgroup.index e).trans (sec_index_tilde hsec h.hEF)
  · exact sec_card_tilde hsec (sup_le (hW.Vn_le_Wn δ h.hδ) (h.hEF.trans h.hFW))
  · have hle : (((Vn δ ⊔ E) ⊓ F).subgroupOf (Wn α)).map hsec.proj ≤ Bt ⊓ j.range := by
      rintro _ ⟨y, hy, rfl⟩
      have hy' : (y : G) ∈ (Vn δ ⊔ E) ⊓ F := hy
      exact ⟨(hBt y).mpr hy'.1, (hrange y).mpr hy'.2⟩
    rw [← sec_card_tilde hsec (inf_le_right.trans h.hFW)]
    exact Subgroup.card_le_of_le hle
  · intro htop
    refine le_antisymm h.hFW fun x hx => ?_
    exact (hrange ⟨x, hx⟩).mp (htop ▸ Subgroup.mem_top _)

theorem S17 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) (hW : W17Hyp α)
    (hM1 : M17Orth) (hM2 : M17Nat) (hδ : δ ∈ nbrs α)
    (hE : stab α ≤ Subgroup.normalizer (E : Set G)) (hF : stab α ≤ Subgroup.normalizer (F : Set G))
    (hZE : Zv α ≤ E) (hEF : E < F) (hFW : F ≤ Wn α)
    (hchief : IsChiefStep (stab α) (Wn α) E F) (hnc : ¬ IsCentralStep (stab α) E F)
    (hC : ∀ w ∈ Wn α, (∀ g ∈ stab α, g * w * g⁻¹ * w⁻¹ ∈ E) → w ∈ E)
    (hVF : Vn δ ⊔ F = Wn α) :
    (∀ q ∈ Qv α, ∀ w ∈ Wn α, q * w * q⁻¹ * w⁻¹ ∈ E) ∧
    (∀ x ∈ Qst δ, ∀ v ∈ Vn δ, x * v * x⁻¹ * v⁻¹ ∈ E) ∧
    E.relIndex (Vn δ ⊔ E) ≤ 4 ∧
    ((IsOrthSec (stab α) E F ∧ F = Wn α) ∨
      (IsNatSec (stab α) E F ∧ F.relIndex (Wn α) ≤ 2 ∧
        E.relIndex ((Vn δ ⊔ E) ⊓ F) ≤ 2)) := by
  have hS : S17Hyp α δ E F := ⟨hδ, hE, hF, hZE, hEF.le, hFW, hC, hVF⟩
  have hq := quot_stab_five hA hs.vα
  have h2 : ∀ x ∈ Qst δ, ∀ v ∈ Vn δ, x * v * x⁻¹ * v⁻¹ ∈ E := fun x hx v hv =>
    hZE (comm_Qst_Vn_mem hA h26 hs hδ hx hv)
  rcases chief_central_or_nat_or_orth hq hW.Wn_le_Qv hchief with hc | ⟨hcs, hnat | horth⟩
  · exact absurd hc hnc
  · obtain ⟨hQ, W, j, B, hj, hequiv, hA5, hCW, hBT, hBtop, hidx, hB, hcardle, -⟩ :=
      S17_core hA h26 hs hW hS hchief hnat hcs nat_fix_alt
    obtain ⟨h31, h32, h33⟩ := hM2 W j.range (MonoidHom.ofInjective hj) hequiv hA5 hCW B hBT hBtop
    refine ⟨hQ, h2, ?_, Or.inr ⟨hnat, ?_, ?_⟩⟩
    · rw [← hB]; exact h32
    · rw [← hidx]; exact h31
    · exact hcardle.trans h33
  · obtain ⟨hQ, W, j, B, hj, hequiv, hA5, hCW, hBT, hBtop, hidx, hB, hcardle, htop⟩ :=
      S17_core hA h26 hs hW hS hchief horth hcs orth_fix_alt
    have hrange : j.range = ⊤ := hM1 W j.range (MonoidHom.ofInjective hj) hequiv hA5 hCW
    refine ⟨hQ, h2, ?_, Or.inl ⟨horth, htop hrange⟩⟩
    rw [← hB]
    have hBB : (B.comap j).map j = B := by rw [Subgroup.map_comap_eq, hrange, top_inf_eq]
    have hfixB : B.comap j ≤ fixW F53Mod.orth S5That := by
      intro u hu
      rw [mem_fixW]
      intro σ hσ
      apply hj
      rw [hequiv]
      exact hBT σ hσ (j u) hu
    calc Nat.card B = Nat.card ((B.comap j).map j) := by rw [hBB]
      _ = Nat.card (B.comap j) := Subgroup.card_map_of_injective hj
      _ ≤ Nat.card (fixW F53Mod.orth S5That) := Subgroup.card_le_of_le hfixB
      _ = 4 := card_fixW_orth_S5That

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
