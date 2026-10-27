module

public import CFSG.Quasithin.Vol2.Ch12Sec7FinD

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative commutatorElement

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem card_autOn_eq_relIndex {V D : Subgroup G} (hDV : D ≤ Subgroup.normalizer (V : Set G)) :
    Nat.card ↥(autOn D V) = (D ⊓ Subgroup.centralizer (V : Set G)).relIndex D :=
  CFSG.Quasithin.AutOn.card_autOn_eq_relIndex hDV

theorem sup_R2_le_normalizer (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V ≤
      Subgroup.normalizer (V : Set G) :=
  sup_le (inf_le_right.trans (Subgroup.centralizer_le_normalizer _))
    (R2_le_normalizer h1222 h)

theorem autOn_sup_le (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    autOn ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V) V ≤
      autOn (R2 T L V) V := by
  have hXN := sup_R2_le_normalizer h1222 h
  have hRN := R2_le_normalizer h1222 h
  have hR2N : R2 T L V ≤ Subgroup.normalizer
      ((Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) :
        Set G) :=
    le_normalizer_inf_centralizer_V (R2_le_M h) hRN
  intro a ha
  obtain ⟨x, rfl⟩ := (A4.mem_autOn_iff hXN).1 ha
  obtain ⟨c, hc, r, hr, hcr⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hR2N).1 x.2
  refine (A4.mem_autOn_iff hRN).2 ⟨⟨r, hr⟩, ?_⟩
  ext v
  rw [A4.actionOn_apply_coe, A4.actionOn_apply_coe]
  have hrv : r * (v : G) * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hRN hr) v).1 v.2
  have hcv := Subgroup.mem_centralizer_iff.1 hc.2 _ hrv
  show r * (v : G) * r⁻¹ = (x : G) * v * (x : G)⁻¹
  rw [hcr]
  calc r * (v : G) * r⁻¹ = c * (r * v * r⁻¹) * c⁻¹ := by rw [← hcv, mul_inv_cancel_right]
    _ = c * r * v * (c * r)⁻¹ := by group

theorem V2_le_of_le_sup (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2) {T L V : Subgroup G}
    (h : Hyp1271 G T L V) {D : Subgroup G}
    (hD : D ≤ (Subgroup.normalizer (L : Set G) ⊓ Subgroup.centralizer (V : Set G)) ⊔ R2 T L V)
    (hVD : V ≤ Subgroup.normalizer (D : Set G))
    (h3 : 2 < (D ⊓ Subgroup.centralizer (V : Set G)).relIndex D) :
    V2 T L V ≤ D ∧ (D ⊓ Subgroup.centralizer (V : Set G)).relIndex D = 4 := by
  obtain ⟨hcomm, -, -⟩ := card_eq_of_1222 h1222 h
  have := hcomm
  have hXN := sup_R2_le_normalizer h1222 h
  have hDN : D ≤ Subgroup.normalizer (V : Set G) := hD.trans hXN
  have hRN := R2_le_normalizer h1222 h
  obtain ⟨-, -, -, -, ⟨-, -, hR4, -, -, hVR⟩, -, -⟩ := h2 G T L V h
  have hle : autOn D V ≤ autOn (R2 T L V) V := (A4.autOn_mono hD).trans (autOn_sup_le h1222 h)
  have hcD := card_autOn_eq_relIndex hDN
  have hdvd : Nat.card ↥(autOn D V) ∣ 4 := hR4 ▸ Subgroup.card_dvd_of_le hle
  have h4 : (D ⊓ Subgroup.centralizer (V : Set G)).relIndex D = 4 := by
    rw [← hcD]
    rw [← hcD] at h3
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    rcases (show Nat.card ↥(autOn D V) = 3 ∨ Nat.card ↥(autOn D V) = 4 by omega) with h | h
    · rw [h] at hdvd
      norm_num at hdvd
    · exact h
  refine ⟨?_, h4⟩
  have heq : autOn D V = autOn (R2 T L V) V :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hR4, hcD, h4])
  rw [← hVR]
  have hVRD : ⁅V, R2 T L V⁆ ≤ ⁅V, D⁆ := by
    refine Subgroup.commutator_le.2 fun v hv r hr => ?_
    have ha : A4.actionOn V (R2 T L V) hRN ⟨r, hr⟩ ∈ autOn D V := by
      rw [heq]
      exact (A4.mem_autOn_iff hRN).2 ⟨⟨r, hr⟩, rfl⟩
    obtain ⟨d, hd⟩ := (A4.mem_autOn_iff hDN).1 ha
    have hdv : (d : G) * v⁻¹ * (d : G)⁻¹ = r * v⁻¹ * r⁻¹ := by
      have := congrArg (fun φ : MulAut ↥V => ((φ ⟨v⁻¹, V.inv_mem hv⟩ : ↥V) : G)) hd
      simpa [A4.actionOn_apply_coe] using this
    have e : ⁅v, r⁆ = ⁅v, (d : G)⁆ := by
      rw [commutatorElement_def, commutatorElement_def]
      calc v * r * v⁻¹ * r⁻¹ = v * (r * v⁻¹ * r⁻¹) := by group
        _ = v * ((d : G) * v⁻¹ * (d : G)⁻¹) := by rw [hdv]
        _ = v * d * v⁻¹ * (d : G)⁻¹ := by group
    rw [e]
    exact Subgroup.commutator_mem_commutator hv d.2
  have hVDD : ⁅V, D⁆ ≤ D := by
    refine Subgroup.commutator_le.2 fun v hv d hd => ?_
    rw [commutatorElement_def]
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.1 (hVD hv) d).1 hd) (D.inv_mem hd)
  exact hVRD.trans hVDD

theorem inf_centralizer_conj_of_mem {D V : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (D : Set G)) :
    D ⊓ Subgroup.centralizer (V.map (MulAut.conj k).toMonoidHom : Set G) =
      (D ⊓ Subgroup.centralizer (V : Set G)).map (MulAut.conj k).toMonoidHom := by
  ext x
  constructor
  · intro hx
    obtain ⟨hxD, hxC⟩ := Subgroup.mem_inf.1 hx
    refine ⟨k⁻¹ * x * k, Subgroup.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hk) x).1 hxD
      simpa using this
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := Subgroup.mem_centralizer_iff.1 hxC (k * a * k⁻¹) ⟨a, ha, rfl⟩
      calc a * (k⁻¹ * x * k) = k⁻¹ * (k * a * k⁻¹ * x) * k := by group
        _ = k⁻¹ * (x * (k * a * k⁻¹)) * k := by rw [h]
        _ = k⁻¹ * x * k * a := by group
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyD, hyC⟩ := Subgroup.mem_inf.1 hy
    refine Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hk y).1 hyD, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h := Subgroup.mem_centralizer_iff.1 hyC a ha
    show k * a * k⁻¹ * (k * y * k⁻¹) = k * y * k⁻¹ * (k * a * k⁻¹)
    calc k * a * k⁻¹ * (k * y * k⁻¹) = k * (a * y) * k⁻¹ := by group
      _ = k * (y * a) * k⁻¹ := by rw [h]
      _ = k * y * k⁻¹ * (k * a * k⁻¹) := by group

theorem map_conj_of_mem_normalizer {D : Subgroup G} {k : G}
    (hk : k ∈ Subgroup.normalizer (D : Set G)) : D.map (MulAut.conj k).toMonoidHom = D := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 hk y).1 hy
  · intro hx
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hk) x).1 hx
      simpa using this
    · show k * (k⁻¹ * x * k) * k⁻¹ = x
      group

theorem isPGroup_sup_conj (h2 : Lemma12_7_2) (h22 : Lemma12_7_22) (h1222 : Stmt12_2_2)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) {D : Subgroup G} {k : G}
    (hV2D : V2 T L V ≤ D) (hidx : (D ⊓ Subgroup.centralizer (V : Set G)).relIndex D = 4)
    (hkD : k ∈ Subgroup.normalizer (D : Set G)) :
    IsPGroup 2 ↥(V ⊔ V.map (MulAut.conj k).toMonoidHom) := by
  obtain ⟨hcomm, -, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  obtain ⟨-, -, -, -, ⟨hV2line, -, -, -, -, -⟩, -, -⟩ := h2 G T L V hS.hyp
  have h16 : Nat.card ↥(V2 T L V) = 16 := hV2line.2
  have hV2V : V2 T L V ≤ V := hV2line.1.1
  set Vk := V.map (MulAut.conj k).toMonoidHom with hVk
  have hidxk : (D ⊓ Subgroup.centralizer (Vk : Set G)).relIndex D = 4 := by
    have h := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj k).toMonoidHom)
      (D ⊓ Subgroup.centralizer (V : Set G)) D (MulAut.conj k).injective
    rw [map_conj_of_mem_normalizer hkD] at h
    rw [hVk, inf_centralizer_conj_of_mem hkD, h, hidx]
  have hle : (V2 T L V ⊓ Subgroup.centralizer (Vk : Set G)).relIndex (V2 T L V) ≤ 4 := by
    rw [Subgroup.inf_relIndex_left]
    rw [Subgroup.inf_relIndex_left] at hidxk
    rw [← hidxk]
    exact Subgroup.relIndex_le_of_le_right hV2D (by rw [hidxk]; norm_num)
  have hmul := Subgroup.relIndex_mul_card (H := V2 T L V ⊓ Subgroup.centralizer (Vk : Set G))
    (K := V2 T L V)
  rw [inf_of_le_left inf_le_left, h16] at hmul
  have hne : V ⊓ Subgroup.centralizer (conjSubgroup V k⁻¹ : Set G) ≠ ⊥ := by
    intro hbot
    have hsub : V2 T L V ⊓ Subgroup.centralizer (Vk : Set G) ≤
        V ⊓ Subgroup.centralizer (conjSubgroup V k⁻¹ : Set G) := by
      have hc : conjSubgroup V k⁻¹ = Vk := by
        rw [hVk, conjSubgroup, inv_inv]
      rw [hc]
      exact inf_le_inf_right _ hV2V
    rw [hbot, le_bot_iff] at hsub
    have h1 : Nat.card ↥(V2 T L V ⊓ Subgroup.centralizer (Vk : Set G)) = 1 := by
      rw [hsub]
      exact Subgroup.card_bot
    rw [h1, mul_one] at hmul
    omega
  have h5 := (h22 G T L V t z hS).2.2.2.2 k⁻¹ hne
  have hc : conjSubgroup V k⁻¹ = Vk := by rw [hVk, conjSubgroup, inv_inv]
  rwa [hc] at h5

end S127

end CFSG.Quasithin.H13
