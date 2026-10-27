module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43Even17Fin

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43'

variable {α : Geo H M}

theorem exists_Qst_of_normalized (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {ε : Geo H M} (hε : ε ∈ nbrs α) {Ψ : ↥(stab α) →* Perm (Fin 5)}
    (hk : Ψ.ker = (Qv α).subgroupOf (stab α))
    (hPS : ((stab α ⊓ stab ε).subgroupOf (stab α)).map Ψ = S5Syl) :
    ∀ τ ∈ S5That, ∃ k : ↥(stab α), (k : G) ∈ Qst ε ∧ Ψ k = τ := by
  obtain ⟨D⟩ := hs.exists_dict hA hε
  obtain ⟨ι, hι⟩ : ∃ ι : Perm (Fin 5) →* Perm (Fin 5), ∀ x : ↥(stab α), ι (D.ψ x) = Ψ x := by
    have hker : D.ψ.ker ≤ Ψ.ker := fun x hx => by
      rw [MonoidHom.mem_ker, D.ker_iff] at hx
      rw [hk]
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
    rw [hk] at hx
    exact (D.ker_iff x).mpr hx
  have hD : ∀ σ ∈ S5Syl, ι σ ∈ S5Syl := by
    intro σ hσ
    rw [← D.bar_S] at hσ
    obtain ⟨x, hxS, rfl⟩ := (D.mem_bar_iff σ).mp hσ
    rw [hι, ← hPS]
    exact ⟨x, hxS, rfl⟩
  intro τ hτ
  obtain ⟨σ, hσT, rfl⟩ := exists_map_S5That hιinj hD hτ
  obtain ⟨k, hk', hkX, hψ⟩ := hs.exists_Qst_of_S5That hA h26 hε D hσT
  exact ⟨⟨k, hkX⟩, hk', by rw [← hι, hψ]⟩

theorem nat_facts (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {E F : Subgroup G} (hnat : IsNatSec (stab α) E F) (hFα : F ≤ stab α)
    (hE : stab α ≤ Subgroup.normalizer (E : Set G)) {ε : Geo H M} (hε : ε ∈ nbrs α) :
    (∀ f₁ ∈ F, ∀ f₂ ∈ F, (∀ k ∈ Qst ε, k * f₁ * k⁻¹ * f₁⁻¹ ∈ E) →
      (∀ k ∈ Qst ε, k * f₂ * k⁻¹ * f₂⁻¹ ∈ E) → f₁ ∉ E → f₂ ∉ E → f₁⁻¹ * f₂ ∈ E) ∧
    (∀ f ∈ F, f ∉ E → (∀ k ∈ Qst ε, k * f * k⁻¹ * f⁻¹ ∈ E) →
      ∀ g ∈ stab α, g * f * g⁻¹ * f⁻¹ ∈ E → g ∈ stab ε) := by
  have hcs : cSecIn (stab α) E F = Qv α :=
    IsModelSec.cSecIn_eq_pCoreOf hnat (quot_stab_five hA hs.vα)
  obtain ⟨hn, θ, β, hθs, hθk, hsd⟩ := hnat
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ :=
    hsd.exists_normalized hθs hθk (sylow_stab_inf_left hA hε)
  have hkΨ' : Ψ.ker = (Qv α).subgroupOf (stab α) := by rw [hkΨ, hcs]
  have hT := exists_Qst_of_normalized hA h26 hs hε hkΨ' hPS
  have hkey : ∀ (g : ↥(stab α)) (f : ↥F) (u : nat.W), β' u = QuotientGroup.mk f →
      (g : G) * f * (g : G)⁻¹ * (f : G)⁻¹ ∈ E → nat.act (Ψ g) u = u := by
    intro g f u hu hgf
    obtain ⟨hgx, h1⟩ := hsd'.equiv g u f hu
    apply hsd'.inj
    rw [h1, hu, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((⟨(g : G) * f * (g : G)⁻¹, hgx⟩ : ↥F)⁻¹ * f : ↥F) : G) =
        (f : G)⁻¹ * ((g : G) * f * (g : G)⁻¹ * (f : G)⁻¹)⁻¹ * (f : G)⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hE (hFα (F.inv_mem f.2))) _).mp (E.inv_mem hgf)
  have hne : ∀ (f : ↥F) (u : nat.W), β' u = QuotientGroup.mk f → (f : G) ∉ E → u ≠ 1 := by
    intro f u hu hfE hu1
    rw [hu1, map_one] at hu
    exact hfE ((QuotientGroup.eq_one_iff f).mp hu.symm)
  have hfix : ∀ (f : ↥F) (u : nat.W), β' u = QuotientGroup.mk f →
      (∀ k ∈ Qst ε, k * f * k⁻¹ * (f : G)⁻¹ ∈ E) → u ∈ fixW nat S5That := by
    intro f u hu hk τ hτ
    obtain ⟨k, hkQ, hkτ⟩ := hT τ hτ
    rw [← hkτ]
    exact hkey k f u hu (hk k hkQ)
  refine ⟨fun f₁ hf₁ f₂ hf₂ hk₁ hk₂ hf₁E hf₂E => ?_, fun f hf hfE hk g hg hgf => ?_⟩
  · obtain ⟨u₁, hu₁⟩ := hsd'.surj (QuotientGroup.mk ⟨f₁, hf₁⟩)
    obtain ⟨u₂, hu₂⟩ := hsd'.surj (QuotientGroup.mk ⟨f₂, hf₂⟩)
    have h := nat_That_unique (hfix _ u₁ hu₁ hk₁) (hfix _ u₂ hu₂ hk₂) (hne _ u₁ hu₁ hf₁E)
      (hne _ u₂ hu₂ hf₂E)
    rw [h, hu₂, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hu₁
    have e : ((⟨f₂, hf₂⟩ : ↥F)⁻¹ * ⟨f₁, hf₁⟩ : ↥F) = (⟨f₂⁻¹ * f₁, F.mul_mem (F.inv_mem hf₂)
        hf₁⟩ : ↥F) := rfl
    rw [e] at hu₁
    have h2 := E.inv_mem hu₁
    simpa using h2
  · obtain ⟨u, hu⟩ := hsd'.surj (QuotientGroup.mk ⟨f, hf⟩)
    have h1 := hkey ⟨g, hg⟩ ⟨f, hf⟩ u hu hgf
    have h2 := nat_That_stab (hfix _ u hu hk) (hne _ u hu hfE) h1
    rw [← hPS] at h2
    obtain ⟨s, hs', hse⟩ := h2
    have h3 : s⁻¹ * ⟨g, hg⟩ ∈ Ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hse, inv_mul_cancel]
    rw [hkΨ', Subgroup.mem_subgroupOf] at h3
    have e : g = (s : G) * ((s⁻¹ * ⟨g, hg⟩ : ↥(stab α)) : G) := by simp
    rw [e]
    exact (stab ε).mul_mem (Subgroup.mem_subgroupOf.mp hs').2
      (Qv_le_stab_of_mem_nbrs hA hε h3)

theorem exists_three (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {β α₂ α' : Geo H M} (hβ : β ∈ nbrs α) (h2 : α₂ ∈ nbrs β) (d2' : dist α' α₂ = 2) {x : G}
    (hx : x ∈ Zv α') (hxα : x ∈ stab α) (hxQ : x ∈ Qst β)
    (hxT : (Zv α ⊓ Subgroup.centralizer ({x} : Set G)).relIndex (Zv α) = 2) :
    ∃ w₁ ∈ Wn α₂, ∃ w₂ ∈ Wn α₂, w₁ ∉ Qv α ∧ w₂ ∉ Qv α ∧ w₁⁻¹ * w₂ ∉ Qv α := by
  obtain ⟨D⟩ := hs.exists_dict hA hβ
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hY := hs.Yv_eq_comm_comm hA h26 hβv (nbrs_symm hβ)
  set τ := D.ψ ⟨x, hxα⟩ with hτ
  have hτT : τ ∈ S5That := by
    refine (D.mem_centralizer_Y_iff ⟨x, hxα⟩).mp ⟨⟨hxα, pCoreOf_le 2 _ hxQ.1⟩, ?_⟩
    rw [← hY]; exact hxQ.2
  have hτ2 : idx orth τ = 2 := by rw [hτ, ← D.relIndex_centralizer_eq]; exact hxT
  obtain ⟨hτ1, hqτ1, hτqτ1⟩ := three_classes (swap_of_That_idx τ hτT hτ2)
  have hqS : qq ∈ D.bar (stab α ⊓ stab β) := by rw [D.bar_S]; exact qq_mem
  obtain ⟨s, hsS, hsq⟩ := (D.mem_bar_iff _).mp hqS
  have hsQ : (s : G) ∈ Qv α ⊔ Qv β := by rw [hs.sup_Qv_edge hA h26 hs.vα hβ]; exact hsS
  have hQβα : Qv β ≤ stab α := Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ)
  obtain ⟨q₁, hq₁, q₂, hq₂, hs12⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
    (hQβα.trans (le_normalizer_pCoreOf 2 (stab α)))).mp hsQ
  have hq₂α : q₂ ∈ stab α := hQβα hq₂
  have hψq : D.ψ ⟨q₂, hq₂α⟩ = qq := by
    have e : s = ⟨q₁, pCoreOf_le 2 _ hq₁⟩ * ⟨q₂, hq₂α⟩ := Subtype.ext hs12
    rw [← hsq, e, map_mul, (D.ker_iff ⟨q₁, _⟩).mpr hq₁, one_mul]
  have hxW : x ∈ Wn α₂ := Sit43.Zv_le_Wn_of_dist d2' hx
  have hq₂2 : q₂ ∈ stab α₂ := Qv_le_stab_of_mem_nbrs hA h2 hq₂
  have hw₂ : q₂ * x * q₂⁻¹ ∈ Wn α₂ :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α₂ hq₂2) x).mp hxW
  have hw₂α : q₂ * x * q₂⁻¹ ∈ stab α :=
    (stab α).mul_mem ((stab α).mul_mem hq₂α hxα) ((stab α).inv_mem hq₂α)
  have hψw₂ : D.ψ ⟨_, hw₂α⟩ = qq * τ * qq⁻¹ := by
    have e : (⟨q₂ * x * q₂⁻¹, hw₂α⟩ : ↥(stab α)) = ⟨q₂, hq₂α⟩ * ⟨x, hxα⟩ * ⟨q₂, hq₂α⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hψq]
  have hnot : ∀ (g : G) (hg : g ∈ stab α), D.ψ ⟨g, hg⟩ ≠ 1 → g ∉ Qv α :=
    fun g hg h hgQ => h ((D.ker_iff ⟨g, hg⟩).mpr hgQ)
  refine ⟨x, hxW, _, hw₂, hnot x hxα hτ1, hnot _ hw₂α (by rw [hψw₂]; exact hqτ1), ?_⟩
  have hm : x⁻¹ * (q₂ * x * q₂⁻¹) ∈ stab α := (stab α).mul_mem ((stab α).inv_mem hxα) hw₂α
  refine hnot _ hm ?_
  have e : (⟨x⁻¹ * (q₂ * x * q₂⁻¹), hm⟩ : ↥(stab α)) = ⟨x, hxα⟩⁻¹ * ⟨_, hw₂α⟩ := rfl
  rw [e, map_mul, map_inv, hψw₂, ← hτ]
  exact hτqτ1

theorem case2_false (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb4 : bMin H M = 4) {β α₂ δ : Geo H M} (hβ : β ∈ nbrs α) (h2 : α₂ ∈ nbrs β)
    (d2 : dist α α₂ = 2) (hδ : δ ∈ nbrs α)
    (hTD : stab α ⊓ stab δ ⊓ (stab α ⊓ stab β ⊓ Subgroup.centralizer (Yv β : Set G)) ≤ Qv α)
    (hV2 : Vn δ ≤ Qv α₂)
    (hw : ∃ w₁ ∈ Wn α₂, ∃ w₂ ∈ Wn α₂, w₁ ∉ Qv α ∧ w₂ ∉ Qv α ∧ w₁⁻¹ * w₂ ∉ Qv α)
    {E F : Subgroup G} (hE : stab α ≤ Subgroup.normalizer (E : Set G))
    (hF : stab α ≤ Subgroup.normalizer (F : Set G)) (hZE : Zv α ≤ E) (hFW : F ≤ Wn α)
    (hR : Vn δ ⊓ E = Zv α) (hD4 : Nat.card (Vn δ) = 2 ^ 6) (hnat : IsNatSec (stab α) E F)
    (hFW2 : F.relIndex (Wn α) ≤ 2) : False := by
  have hG := hA.amalgam.gen
  have hb : 3 ≤ bMin H M := by omega
  have h2v : vtype α₂ = false := hs.vtype_of_dist_two hA (by rw [CosetGeom.dist_comm]; exact d2)
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hδv : vtype δ = true := Sit43.vtype_true_of_adj hs.vα hδ
  have hWα : Wn α ≤ stab α := (hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)
  have hFα : F ≤ stab α := hFW.trans hWα
  have hEc : ∀ {g y : G}, g ∈ stab α → y ∈ E → g * y * g⁻¹ ∈ E := fun hg hy =>
    (Subgroup.mem_normalizer_iff.mp (hE hg) _).mp hy
  obtain ⟨hnatβ, -⟩ := nat_facts hA h26 hs hnat hFα hE hβ
  obtain ⟨-, hnatδ⟩ := nat_facts hA h26 hs hnat hFα hE hδ
  obtain ⟨v, hvV, hvF, hvE⟩ : ∃ v ∈ Vn δ, v ∈ F ∧ v ∉ E := by
    by_contra hcon
    push Not at hcon
    have hle : Vn δ ⊓ F ≤ Zv α := fun v hv => hR ▸ ⟨hv.1, hcon v hv.1 hv.2⟩
    have h4 := hs.relIndex_Zv_Vn hs.vα hδ hD4
    have h1 : (Zv α).relIndex (Vn δ) ≤ (Vn δ ⊓ F).relIndex (Vn δ) :=
      Subgroup.relIndex_le_of_le_left hle (relIndex_ne_zero_of_finite _ _)
    have h3 : (Vn δ ⊓ F).relIndex (Vn δ) ≤ F.relIndex (Wn α) := by
      rw [inf_comm, Subgroup.inf_relIndex_right]
      exact Subgroup.relIndex_le_of_le_right (hs.Vn_le_Wn hA h26 hδ)
        (relIndex_ne_zero_of_finite _ _)
    omega
  have hvQδ : ∀ k ∈ Qst δ, k * v * k⁻¹ * v⁻¹ ∈ E := fun k hk =>
    hZE (hs.comm_Qst_Vn_mem hA h26 hδ hk hvV)
  have hl : ∀ l : Geo H M, dist l α₂ = 2 → vtype l = false ∧ dist l α ≤ 4 ∧ dist l β ≤ 3 := by
    intro l hl
    have t1 := CosetGeom.dist_triangle hG l α₂ α
    have t2 := CosetGeom.dist_triangle hG l α₂ β
    have e1 : dist α₂ β = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm h2)
    rw [CosetGeom.dist_comm α₂ α] at t1
    exact ⟨(hs.of_vtype_false h2v).vtype_of_dist_two hA hl, by omega, by omega⟩
  have hW2 : Wn α₂ ≤ stab α := iSup₂_le fun l hl' =>
    hs.Zv_le_stab_of_dist_le_false hA (hl l hl').1 (by rw [hb4]; exact (hl l hl').2.1)
  have hW2β : Wn α₂ ≤ Qv β := iSup₂_le fun l hl' =>
    hs.Zv_le_Qv_of_dist_lt_false (hl l hl').1 (by rw [hb4]; have := (hl l hl').2.2; omega)
  have hW22 : Wn α₂ ≤ Qv α₂ := (hs.of_vtype_false h2v).Wn_le_Qv hA hb
  have hD4β : Nat.card (Vn β) = 2 ^ 6 := (card_Vn_eq hβv hδv).trans hD4
  have hWQ := hs.comm_Wn_Qv_le hA h26 hb h2v (nbrs_symm h2) hD4β
  have hcZ : ∀ w ∈ Wn α₂, w * v * w⁻¹ * v⁻¹ ∈ Zv α₂ := fun w hw => by
    have h1 := hWQ (Subgroup.commutator_mem_commutator hw (hV2 hvV))
    rwa [commutatorElement_def] at h1
  have hcF : ∀ w ∈ Wn α₂, w * v * w⁻¹ * v⁻¹ ∈ F := fun w hw =>
    F.mul_mem ((Subgroup.mem_normalizer_iff.mp (hF (hW2 hw)) v).mp hvF) (F.inv_mem hvF)
  have hcβ : ∀ w ∈ Wn α₂, ∀ k ∈ Qst β,
      k * (w * v * w⁻¹ * v⁻¹) * k⁻¹ * (w * v * w⁻¹ * v⁻¹)⁻¹ ∈ E := fun w hw k hk =>
    hZE (hs.comm_Qst_Vn_mem hA h26 hβ hk (Sit43.Zv_le_Vn_nbrs h2 (hcZ w hw)))
  have hKQ : ∀ w ∈ Wn α₂, w * v * w⁻¹ * v⁻¹ ∈ E → w ∈ Qv α := by
    intro w hw hwE
    have hwδ := hnatδ v hvF hvE hvQδ w (hW2 hw) hwE
    have hwC : w ∈ Subgroup.centralizer (Yv β : Set G) := fun y hy =>
      Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α₂ (hW22 hw)) y
        (Yv_le_Zv h2 hy)
    exact hTD ⟨⟨hW2 hw, hwδ⟩, ⟨⟨hW2 hw, pCoreOf_le 2 _ (hW2β hw)⟩, hwC⟩⟩
  obtain ⟨w₁, hw₁, w₂, hw₂, h1, h2', h3⟩ := hw
  have hn₁ : w₁ * v * w₁⁻¹ * v⁻¹ ∉ E := fun h => h1 (hKQ w₁ hw₁ h)
  have hn₂ : w₂ * v * w₂⁻¹ * v⁻¹ ∉ E := fun h => h2' (hKQ w₂ hw₂ h)
  have hc := hnatβ _ (hcF w₁ hw₁) _ (hcF w₂ hw₂) (hcβ w₁ hw₁) (hcβ w₂ hw₂) hn₁ hn₂
  apply h3
  refine hKQ _ ((Wn α₂).mul_mem ((Wn α₂).inv_mem hw₁) hw₂) ?_
  have e : (w₁⁻¹ * w₂) * v * (w₁⁻¹ * w₂)⁻¹ * v⁻¹ =
      (w₁⁻¹ * (w₁ * v * w₁⁻¹ * v⁻¹)) * ((w₁ * v * w₁⁻¹ * v⁻¹)⁻¹ * (w₂ * v * w₂⁻¹ * v⁻¹)) *
        (w₁⁻¹ * (w₁ * v * w₁⁻¹ * v⁻¹))⁻¹ := by group
  rw [e]
  exact hEc ((stab α).mul_mem ((stab α).inv_mem (hW2 hw₁)) (hFα (hcF w₁ hw₁))) hc

end Sit43'

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
