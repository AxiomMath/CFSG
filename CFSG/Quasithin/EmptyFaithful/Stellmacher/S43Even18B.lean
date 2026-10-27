module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenDefs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace C18

variable {α β : Geo H M}

theorem Wn_le_normalizer_Zv (hA : F53Amalgam H M S) (hWs : Wn α ≤ stab α) :
    Wn α ≤ Subgroup.normalizer (Zv α : Set G) :=
  hWs.trans (stab_le_normalizer_Zv hA α)

theorem mem_Estar_iff (hA : F53Amalgam H M S) (hWs : Wn α ≤ stab α) {y : G} :
    y ∈ Estar α ↔ y ∈ Wn α ∧ ∀ g ∈ stab α, g * y * g⁻¹ * y⁻¹ ∈ Zv α :=
  mem_fixSecIn_iff (Wn_le_normalizer_Zv hA hWs)

theorem Estar_le_Wn (hA : F53Amalgam H M S) (hWs : Wn α ≤ stab α) : Estar α ≤ Wn α :=
  fun _ hy => ((mem_Estar_iff hA hWs).mp hy).1

theorem Zv_le_Estar (hA : F53Amalgam H M S) (hWs : Wn α ≤ stab α) (hZW : Zv α ≤ Wn α) :
    Zv α ≤ Estar α := fun z hz =>
  (mem_Estar_iff hA hWs).mpr ⟨hZW hz, fun _ hg => (Zv α).mul_mem
    ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hg) z).mp hz)
    ((Zv α).inv_mem hz)⟩

theorem stab_le_normalizer_Estar (hA : F53Amalgam H M S) (hWs : Wn α ≤ stab α) :
    stab α ≤ Subgroup.normalizer (Estar α : Set G) := by
  refine Sit43.le_normalizer_of_conj_mem fun g hg y hy => ?_
  obtain ⟨hyW, hy'⟩ := (mem_Estar_iff hA hWs).mp hy
  refine (mem_Estar_iff hA hWs).mpr ⟨(Subgroup.mem_normalizer_iff.mp
    (stab_le_normalizer_Wn α hg) y).mp hyW, fun a ha => ?_⟩
  have hb : g⁻¹ * a * g ∈ stab α := (stab α).mul_mem ((stab α).mul_mem
    ((stab α).inv_mem hg) ha) hg
  have h1 := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hg) _).mp (hy' _ hb)
  have e : g * (g⁻¹ * a * g * y * (g⁻¹ * a * g)⁻¹ * y⁻¹) * g⁻¹ =
      a * (g * y * g⁻¹) * a⁻¹ * (g * y * g⁻¹)⁻¹ := by group
  rwa [e] at h1

theorem comm_Estar_Lres_le (hA : F53Amalgam H M S) (hWs : Wn α ≤ stab α) :
    ⁅Estar α, Lres α⁆ ≤ Zv α := by
  rw [Subgroup.commutator_le]
  intro e he l hl
  have h1 := ((mem_Estar_iff hA hWs).mp he).2 l (oTwoRes_le _ hl)
  have e1 : ⁅e, l⁆ = (l * e * l⁻¹ * e⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
  rw [e1]
  exact (Zv α).inv_mem h1

theorem Vn_inf_Estar_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) : Vn β ⊓ Estar α = Zv α := by
  have hWs : Wn α ≤ stab α := (hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)
  exact hs.S13' hA h26 (stab_le_normalizer_Estar hA hWs)
    (Zv_le_Estar hA hWs (hs.Zv_le_Wn hA h26)) (comm_Estar_Lres_le hA hWs) hβ

omit [Finite G] in
theorem mem_fixSecIn_iff_of_secData {n : ℕ} {Mo : Model n} {K L X : Subgroup G}
    [(L.subgroupOf X).Normal] {Ψ : ↥K →* Perm (Fin n)} {β' : Mo.W →* ↥X ⧸ L.subgroupOf X}
    (h : SecData Mo K L X Ψ β') (hLX : L ≤ X) {A : Subgroup G} (hAK : A ≤ K) {u : Mo.W}
    {x : ↥X} (hu : β' u = QuotientGroup.mk x) :
    (x : G) ∈ fixSecIn A L X ↔ u ∈ fixW Mo ((A.subgroupOf K).map Ψ) := by
  rw [X1512.mem_fixSecIn hLX]
  constructor
  · rintro ⟨-, hx⟩
    rintro σ ⟨a', ha', rfl⟩
    obtain ⟨hax, h'⟩ := h.equiv a' u x hu
    apply h.inj
    rw [h', hu]
    exact ((X1512.mk_eq_iff hLX).mpr (hx a' (Subgroup.mem_subgroupOf.mp ha'))).symm
  · intro hfix
    refine ⟨x.2, fun a ha => ?_⟩
    have haK : a ∈ K := hAK ha
    obtain ⟨hax, h'⟩ := h.equiv ⟨a, haK⟩ u x hu
    have h2 := hfix (Ψ ⟨a, haK⟩) ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
    rw [h2, hu] at h'
    exact (X1512.mk_eq_iff hLX).mp h'

theorem exists_normalized_orth (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) {N : Subgroup G} (hN : IsOrthSec (stab α) (Zv α) N) :
    ∃ (_ : ((Zv α).subgroupOf N).Normal) (Ψ : ↥(stab α) →* Perm (Fin 5))
      (β' : orth.W →* ↥N ⧸ (Zv α).subgroupOf N),
      Function.Surjective Ψ ∧ Ψ.ker = (Qv α).subgroupOf (stab α) ∧
      SecData orth (stab α) (Zv α) N Ψ β' ∧
      ((stab α ⊓ stab β).subgroupOf (stab α)).map Ψ = S5Syl ∧
      S5That ≤ ((Qst β).subgroupOf (stab α)).map Ψ := by
  have hcs : cSecIn (stab α) (Zv α) N = Qv α :=
    IsModelSec.cSecIn_eq_pCoreOf hN (quot_stab_five hA hs.vα)
  obtain ⟨hn, θ, β₀, hθs, hθk, hsd⟩ := hN
  obtain ⟨Ψ, β', hΨs, hkΨ, hsd', hPS, -⟩ :=
    hsd.exists_normalized hθs hθk (sylow_stab_inf_left hA hβ)
  have hkΨ' : Ψ.ker = (Qv α).subgroupOf (stab α) := by rw [hkΨ, hcs]
  refine ⟨hn, Ψ, β', hΨs, hkΨ', hsd', hPS, ?_⟩
  obtain ⟨D⟩ := hs.exists_dict hA hβ
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
  intro τ hτ
  obtain ⟨σ, hσT, rfl⟩ := exists_map_S5That hιinj hD hτ
  obtain ⟨k, hk', hkX, hψ⟩ := hs.exists_Qst_of_S5That hA h26 hβ D hσT
  exact ⟨⟨k, hkX⟩, Subgroup.mem_subgroupOf.mpr hk', by rw [← hι, hψ]⟩

theorem Zv_le_fixSecIn (hA : F53Amalgam H M S) {N A : Subgroup G} (hZN : Zv α ≤ N)
    (hNs : N ≤ stab α) (hAs : A ≤ stab α) : Zv α ≤ fixSecIn A (Zv α) N := fun z hz =>
  (mem_fixSecIn_iff (hNs.trans (stab_le_normalizer_Zv hA α))).mpr ⟨hZN hz, fun _ ha =>
    (Zv α).mul_mem ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α (hAs ha)) z).mp
      hz) ((Zv α).inv_mem hz)⟩

theorem relIndex_fixSecIn_Qst_le (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hβ : β ∈ nbrs α) {N : Subgroup G} (hN : IsOrthSec (stab α) (Zv α) N) (hZN : Zv α ≤ N)
    (hNs : N ≤ stab α) : (Zv α).relIndex (fixSecIn (Qst β) (Zv α) N) ≤ 4 := by
  obtain ⟨hn, Ψ, β', hΨs, hkΨ, hsd, hPS, hT⟩ := exists_normalized_orth hA h26 hs hβ hN
  have hQs : Qst β ≤ stab α := inf_le_left.trans (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ))
  have h1 := hsd.relIndex_fixSecIn hZN hQs
  have h2 := hsd.relIndex_eq
  rw [card_orth] at h2
  have hfle : fixW orth (((Qst β).subgroupOf (stab α)).map Ψ) ≤ fixW orth S5That :=
    fun w hw σ hσ => hw σ (hT hσ)
  have h3 : (fixW orth S5That).index = 4 := by
    have h := Subgroup.card_mul_index (fixW orth S5That)
    rw [card_fixW_orth_S5That, card_orth] at h
    omega
  have h4 : 4 ≤ (fixSecIn (Qst β) (Zv α) N).relIndex N := by
    rw [h1, ← h3]
    exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite)
      (Subgroup.index_dvd_of_le hfle)
  have hZF := Zv_le_fixSecIn hA hZN hNs hQs
  have hFN : fixSecIn (Qst β) (Zv α) N ≤ N := fun y hy =>
    ((mem_fixSecIn_iff (hNs.trans (stab_le_normalizer_Zv hA α))).mp hy).1
  have hmul := Subgroup.relIndex_mul_relIndex (Zv α) (fixSecIn (Qst β) (Zv α) N) N hZF hFN
  rw [h2] at hmul
  have hpos : 0 < (Zv α).relIndex (fixSecIn (Qst β) (Zv α) N) :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  by_contra hcon
  push Not at hcon
  nlinarith

theorem proj_eq (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) (hβ : β ∈ nbrs α) {N : Subgroup G} (hN : IsOrthSec (stab α) (Zv α) N)
    (hsup : Estar α ⊔ N = Wn α) (hinf : Estar α ⊓ N = Zv α) (hD4 : Nat.card (Vn β) = 2 ^ 6) :
    (Vn β ⊔ Estar α) ⊓ N = fixSecIn (Qst β) (Zv α) N := by
  have hWs : Wn α ≤ stab α := (hs.Wn_le_Qv hA hb).trans (pCoreOf_le 2 _)
  have hNW : N ≤ Wn α := hsup ▸ le_sup_right
  have hNs : N ≤ stab α := hNW.trans hWs
  have hZN : Zv α ≤ N := hinf ▸ inf_le_right
  have hEn := stab_le_normalizer_Estar hA hWs
  have hVE := Vn_inf_Estar_eq hA h26 hs hb hβ
  have hVW : Vn β ≤ Wn α := hs.Vn_le_Wn hA h26 hβ
  have hVEn : Vn β ≤ Subgroup.normalizer (Estar α : Set G) := (hVW.trans hWs).trans hEn
  have hNEn : N ≤ Subgroup.normalizer (Estar α : Set G) := hNs.trans hEn
  have hNZ : N ≤ Subgroup.normalizer (Zv α : Set G) := hNs.trans (stab_le_normalizer_Zv hA α)
  have hQs : Qst β ≤ stab α := inf_le_left.trans (Qv_le_stab_of_mem_nbrs hA (nbrs_symm hβ))
  have hle : (Vn β ⊔ Estar α) ⊓ N ≤ fixSecIn (Qst β) (Zv α) N := by
    intro y hy
    refine (mem_fixSecIn_iff hNZ).mpr ⟨hy.2, fun q hq => ?_⟩
    have hy1 : y ∈ Estar α ⊔ Vn β := by rw [sup_comm]; exact hy.1
    obtain ⟨e, he, v, hv, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hVEn).mp hy1
    have h1 : q * e * q⁻¹ * e⁻¹ ∈ Zv α := ((mem_Estar_iff hA hWs).mp he).2 q (hQs hq)
    have h2 : q * v * q⁻¹ * v⁻¹ ∈ Zv α := hs.comm_Qst_Vn_mem hA h26 hβ hq hv
    have h3 : e * (q * v * q⁻¹ * v⁻¹) * e⁻¹ ∈ Zv α :=
      (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α
        (hWs (Estar_le_Wn hA hWs he))) _).mp h2
    have e1 : q * (e * v) * q⁻¹ * (e * v)⁻¹ =
        (q * e * q⁻¹ * e⁻¹) * (e * (q * v * q⁻¹ * v⁻¹) * e⁻¹) := by group
    rw [e1]
    exact (Zv α).mul_mem h1 h3
  set P := (Vn β ⊔ Estar α) ⊓ N with hP
  have hZP : Zv α ≤ P := le_inf ((Sit43.Zv_le_Vn hβ).trans le_sup_left) hZN
  have hPE : Estar α ⊓ P = Zv α := by
    apply le_antisymm
    · rw [← hinf]
      exact inf_le_inf_left _ inf_le_right
    · exact le_inf (Zv_le_Estar hA hWs (hs.Zv_le_Wn hA h26)) hZP
  have hPsup : P ⊔ Estar α = Vn β ⊔ Estar α := by
    apply le_antisymm (sup_le inf_le_left le_sup_right)
    refine sup_le (fun v hv => ?_) le_sup_right
    have hvW : v ∈ Estar α ⊔ N := hsup ▸ hVW hv
    obtain ⟨e, he, n, hn, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hNEn).mp hvW
    have hnP : n ∈ P := by
      refine ⟨?_, hn⟩
      have e1 : n = e⁻¹ * (e * n) := by group
      rw [e1]
      exact (Vn β ⊔ Estar α).mul_mem ((le_sup_right : Estar α ≤ Vn β ⊔ Estar α)
        ((Estar α).inv_mem he)) ((le_sup_left : Vn β ≤ Vn β ⊔ Estar α) hv)
    exact (P ⊔ Estar α).mul_mem ((le_sup_right : Estar α ≤ P ⊔ Estar α) he)
      ((le_sup_left : P ≤ P ⊔ Estar α) hnP)
  have hPn : P ≤ Subgroup.normalizer (Estar α : Set G) := inf_le_right.trans hNEn
  have h4 : (Zv α).relIndex P = 4 := by
    rw [← hPE, Subgroup.inf_relIndex_right, ← relIndex_sup_eq_of_le_normalizer hPn, hPsup,
      relIndex_sup_eq_of_le_normalizer hVEn, ← Subgroup.inf_relIndex_right, inf_comm, hVE]
    exact hs.relIndex_Zv_Vn hs.vα hβ hD4
  have hfix := relIndex_fixSecIn_Qst_le hA h26 hs hβ hN hZN hNs
  have hFN : fixSecIn (Qst β) (Zv α) N ≤ N := fun y hy => ((mem_fixSecIn_iff hNZ).mp hy).1
  have hmul := Subgroup.relIndex_mul_relIndex (Zv α) P (fixSecIn (Qst β) (Zv α) N) hZP hle
  rw [h4] at hmul
  have hone : P.relIndex (fixSecIn (Qst β) (Zv α) N) = 1 := by
    have hpos : 0 < P.relIndex (fixSecIn (Qst β) (Zv α) N) :=
      Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    omega
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

end C18

end CFSG.Quasithin.F53.Stellmacher.S43.Even
