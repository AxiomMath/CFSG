module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenFaithful
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenStepTwo
public import CFSG.LocalAnalysis.WeakClosure81.SevenEightCoreBar
public import CFSG.LocalAnalysis.WeakClosure81.EightNineAS
import CFSG.LocalAnalysis.WeakClosure81.EightNineteenAux
public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPFinite

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

private theorem wc813psa_omegaOneCenterOf_ne_bot {T : Subgroup G} (hT : IsPGroup 2 T)
    (hT1 : T ≠ ⊥) : omegaOneCenterOf T ≠ ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Nontrivial ↥T := (Subgroup.nontrivial_iff_ne_bot T).2 hT1
  have hZ : Nontrivial (Subgroup.center ↥T) := hT.center_nontrivial
  obtain ⟨n, hn, hcard⟩ := ((hT.to_subgroup (Subgroup.center ↥T)).nontrivial_iff_card).1 hZ
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥T) 2
    (by rw [hcard]; exact dvd_pow_self 2 hn.ne')
  intro hbot
  have hmem : ((z : ↥T) : G) ∈ omegaOneCenterOf T := by
    apply Subgroup.subset_closure
    refine ⟨⟨(z : ↥T).2, Subgroup.mem_centralizer_iff.2 fun h hh => ?_⟩, ?_⟩
    · exact congrArg Subtype.val (Subgroup.mem_center_iff.1 z.2 ⟨h, hh⟩)
    · have h2 : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have h3 := congrArg (fun w : Subgroup.center ↥T => ((w : ↥T) : G)) h2
      simpa using h3
  rw [hbot, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

private theorem wc813psa_isSylowIn_subgroupOf_top {p : ℕ} {T H : Subgroup G}
    (h : IsSylowIn p T H) : IsSylowIn p (T.subgroupOf H) ⊤ := by
  refine ⟨le_top, ?_, ?_⟩
  · exact h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm
  · have h1 : T.relIndex H = (T.subgroupOf H).relIndex ⊤ := by
      rw [Subgroup.relIndex_top_right]
      rfl
    rw [← h1]
    exact h.not_dvd_relIndex

private theorem wc813psa_conj_mem_cGrp {H T : Subgroup G} {h n : G} (hh : h ∈ H)
    (hn : n ∈ cGrp H T) : h * n * h⁻¹ ∈ cGrp H T := by
  obtain ⟨hnH, hnC⟩ := Subgroup.mem_inf.mp hn
  refine Subgroup.mem_inf.mpr ⟨H.mul_mem (H.mul_mem hh hnH) (H.inv_mem hh), ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hnC ⊢
  intro e he
  have hhe : h⁻¹ * e * h ∈ eGrp H T := by
    have hmem := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_conjClosure (omegaOneCenterOf T) H (H.inv_mem hh)) e).1 he
    simpa [inv_inv, eGrp] using hmem
  have hnC' := hnC (h⁻¹ * e * h) hhe
  have key : h * n * h⁻¹ * e = e * (h * n * h⁻¹) := by
    calc h * n * h⁻¹ * e = h * (n * (h⁻¹ * e * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * e * h) * n) * h⁻¹ := by rw [← hnC']
      _ = e * (h * n * h⁻¹) := by group
  exact key.symm

private theorem wc813psa_barSub_inf_of_le {H C Y A : Subgroup G} {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H C φ) (hCY : C ≤ Y) :
    barSub H φ A ⊓ barSub H φ Y = barSub H φ (A ⊓ Y) := by
  refine le_antisymm ?_ (le_inf
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_left))
    (Subgroup.map_mono (Subgroup.subgroupOf_mono H inf_le_right)))
  intro x hx
  obtain ⟨hxA, hxY⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨a, haA, haφ⟩ := mem_barSub.mp hxA
  obtain ⟨y, hyY, hyφ⟩ := mem_barSub.mp hxY
  have hker : φ (a * y⁻¹) = 1 := by rw [map_mul, map_inv, haφ, hyφ, mul_inv_cancel]
  have hmemC : ((a * y⁻¹ : ↥H) : G) ∈ C := (hφ.ker_iff (a * y⁻¹)).mp hker
  have hmemY : ((a * y⁻¹ : ↥H) : G) ∈ Y := hCY hmemC
  have haY : (a : G) ∈ Y := by
    have h2 : ((a * y⁻¹ : ↥H) : G) * (y : G) = (a : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [← h2]
    exact Y.mul_mem hmemY hyY
  exact mem_barSub.mpr ⟨a, Subgroup.mem_inf.mpr ⟨haA, haY⟩, haφ⟩

private theorem wc813psa_conjSubgroup_barSub {H B : Subgroup G} {Q : Type} [Group Q]
    (φ : ↥H →* Q) {g : ↥H} :
    conjSubgroup (barSub H φ B) (φ g) = barSub H φ (conjSubgroup B (g : G)) := by
  ext x
  constructor
  · intro hx
    have hx' : φ g * x * (φ g)⁻¹ ∈ barSub H φ B := mem_conjSubgroup_iff.mp hx
    obtain ⟨b, hbB, hbφ⟩ := mem_barSub.mp hx'
    refine mem_barSub.mpr ⟨g⁻¹ * b * g, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have hcoe : (g : G) * (↑(g⁻¹ * b * g) : G) * (g : G)⁻¹ = (b : G) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hcoe]
      exact hbB
    · rw [map_mul, map_mul, map_inv]
      have hb' : φ b = φ g * x * (φ g)⁻¹ := hbφ
      rw [hb']
      group
  · intro hx
    obtain ⟨a, haB, haφ⟩ := mem_barSub.mp hx
    have ha' : (g : G) * (a : G) * (g : G)⁻¹ ∈ B := mem_conjSubgroup_iff.mp haB
    refine mem_conjSubgroup_iff.mpr ?_
    refine mem_barSub.mpr ⟨g * a * g⁻¹, ha', ?_⟩
    rw [map_mul, map_mul, map_inv, haφ]

structure Pre813 (V H T : Subgroup G) (i : ℕ) (A : Subgroup G) : Prop where
  minCex : MinCex88 V H T i
  calH0 : IsCalH0 V H
  mem : A ∈ E3.gammaSet V i T
  notLe : ∃ x ∈ H, ¬ conjSubgroup A x ≤ normalizer (V : Set G)
  concl812 : Concl812 V H T i A

theorem Sit813.toPre {V H T A L K : Subgroup G} {i : ℕ} (h : Sit813 V H T i A L K) :
    Pre813 V H T i A :=
  ⟨h.minCex, h.calH0, h.mem, h.notLe, h.concl812⟩

theorem cGrp_le_kerMV (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) {V H T A : Subgroup G} {i : ℕ}
    (h : Pre813 V H T i A) : cGrp H T ≤ kerMV V H := by
  have hH : IsCalH V H := h.calH0.1
  have hV : IsElemAbelian 2 V := h.minCex.hyp.hyp7.1
  have hVne : V ≠ ⊥ := by
    intro hb
    have h2 := h.minCex.hyp.hyp7.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH h.minCex.hyp.sylow
  have hVT : V ≤ T := le_of_isCalH hV hH h.minCex.hyp.sylow
  have hTne : T ≠ ⊥ := fun hb => hVne (le_bot_iff.mp (hVT.trans (le_of_eq hb)))
  have hCn : ∀ a ∈ H, ∀ n ∈ cGrp H T, a * n * a⁻¹ ∈ cGrp H T :=
    fun _ ha _ hn => wc813psa_conj_mem_cGrp ha hn
  have hCM : cGrp H T ≤ normalizer (V : Set G) := by
    have hCsupH : cGrp H T ⊔ T ≤ H := sup_le inf_le_left hTH.le
    have hCsup_ne : cGrp H T ⊔ T ≠ H := by
      intro hsup
      obtain ⟨z, hz1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
        (wc813psa_omegaOneCenterOf_ne_bot hTH.isPGroup hTne)
      have hzZ : (z : G) ∈ omegaOneCenterOf T := z.2
      have hzT : (z : G) ∈ T := omegaOneCenterOf_le T hzZ
      have hz1 : (z : G) ≠ 1 := fun hh => hz1' (Subtype.ext hh)
      have hzE : (z : G) ∈ eGrp H T := le_conjClosure _ _ hzZ
      have hzC : ∀ t ∈ T, (z : G) * t = t * (z : G) := fun t ht =>
        (mem_centralizer_of_mem_omegaOneCenterOf hzZ ht).symm
      have hCcen : cGrp H T ≤ centralizer ({(z : G)} : Set G) := by
        intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 (z : G) hzE
      have hTcen : T ≤ centralizer ({(z : G)} : Set G) := by
        intro t ht
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hzC t ht
      have hHz : H ≤ centralizer ({(z : G)} : Set G) := by
        have h1 : cGrp H T ⊔ T ≤ H ⊓ centralizer ({(z : G)} : Set G) :=
          sup_le (le_inf inf_le_left hCcen) (le_inf hTH.le hTcen)
        rw [hsup] at h1
        exact h1.trans inf_le_right
      exact h.minCex.hyp.notLe
        (le_trans (le_inf le_rfl hHz) (h.minCex.hyp.centr (z : G) hzT hzC hz1))
    have hCsup_lt : cGrp H T ⊔ T < H := lt_of_le_of_ne hCsupH hCsup_ne
    obtain ⟨X, hX, hCX⟩ := exists_mem_calNIn_of_lt (T := T) (H := H) (Y := cGrp H T ⊔ T)
      le_sup_right hCsup_lt
    have hXmem := hX
    rw [MinCex88.calNIn_eq_AS h5_11 h5_13 h.minCex] at hXmem
    have hXeq : X = H ⊓ normalizer (V : Set G) := Set.mem_singleton_iff.mp hXmem
    have hCX' : cGrp H T ≤ X := le_sup_left.trans hCX
    rw [hXeq] at hCX'
    exact hCX'.trans inf_le_right
  exact le_kerMV_of_normal inf_le_left hCn hCM

theorem no_normal_two_bar {V H T A : Subgroup G} {i : ℕ} (h : Pre813 V H T i A)
    {Q : Type} [Group Q] {φ : ↥H →* Q} (hφ : IsBarMap H (cGrp H T) φ) :
    ∀ P : Subgroup Q, P.Normal → IsPGroup 2 P → P = ⊥ := by
  intro P hPN hP2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Q := Finite.of_surjective φ hφ.surjective
  have hH : IsCalH V H := h.calH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH h.minCex.hyp.sylow
  have hTbSyl : IsSylowIn 2 (barSub H φ T) ⊤ := by
    have hsub := wc813psa_isSylowIn_subgroupOf_top hTH
    have hmap := E1.isSylowIn_two_map_top hφ.surjective hsub
    simpa [barSub] using hmap
  have hPle : P ≤ barSub H φ T :=
    hTbSyl.le_of_normal le_top (hPN.subgroupOf ⊤) hP2
  set P' : Subgroup G := barPre H φ P with hP'def
  have hP'H : P' ≤ H := barPre_le H φ P
  have hP'sub : P'.subgroupOf H = P.comap φ := by
    change (((P.comap φ).map H.subtype).subgroupOf H) = P.comap φ
    rw [← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hP'N : (P'.subgroupOf H).Normal := by
    rw [hP'sub]
    exact hPN.comap φ
  have hP'TC : ∀ g ∈ P', ∃ t ∈ T, ∃ c ∈ cGrp H T, g = t * c := by
    intro g hg
    obtain ⟨hgH, hφgP⟩ := mem_barPre.mp hg
    obtain ⟨t, htT, htφ⟩ := mem_barSub.mp (hPle hφgP)
    refine ⟨(t : G), htT, ((t⁻¹ * ⟨g, hgH⟩ : ↥H) : G), ?_, ?_⟩
    · have h1 : φ (t⁻¹ * ⟨g, hgH⟩) = 1 := by
        rw [map_mul, map_inv, htφ]
        simp
      exact (hφ.ker_iff (t⁻¹ * ⟨g, hgH⟩)).mp h1
    · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
  have hcomm_z : ∀ g ∈ P', ∀ z' ∈ omegaOneCenterOf T, g * z' = z' * g := by
    intro g hg z' hz'
    obtain ⟨t, htT, c, hcC, rfl⟩ := hP'TC g hg
    have ht : t * z' = z' * t := mem_centralizer_of_mem_omegaOneCenterOf hz' htT
    have hc : c * z' = z' * c :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hcC).2 z'
        (le_conjClosure _ _ hz')).symm
    calc t * c * z' = t * (c * z') := by group
      _ = t * (z' * c) := by rw [hc]
      _ = (t * z') * c := by group
      _ = (z' * t) * c := by rw [ht]
      _ = z' * (t * c) := by group
  have hP'Nconj : ∀ g ∈ P', ∀ a ∈ H, a * g * a⁻¹ ∈ P' := by
    intro g hg a ha
    have h1 : (⟨a, ha⟩ : ↥H) * ⟨g, hP'H hg⟩ * (⟨a, ha⟩ : ↥H)⁻¹ ∈ P'.subgroupOf H :=
      hP'N.conj_mem ⟨g, hP'H hg⟩ (by simpa [Subgroup.mem_subgroupOf] using hg) ⟨a, ha⟩
    simpa [Subgroup.mem_subgroupOf] using h1
  have hcen : P' ≤ centralizer (eGrp H T : Set G) := by
    rw [eGrp, conjClosure, Subgroup.centralizer_closure]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    rintro y ⟨a, ha, z', hz', rfl⟩
    have hg₁ : a⁻¹ * g * a ∈ P' := by
      simpa [inv_inv] using hP'Nconj g hg a⁻¹ (H.inv_mem ha)
    have hz'' := hcomm_z (a⁻¹ * g * a) hg₁ z' hz'
    calc (a * z' * a⁻¹) * g
        = a * (z' * (a⁻¹ * g * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * g * a) * z') * a⁻¹ := by rw [← hz'']
      _ = g * (a * z' * a⁻¹) := by group
  have hP'C : P' ≤ cGrp H T := le_inf hP'H hcen
  have hbarP' : barSub H φ P' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨g, hgP', rfl⟩ := mem_barSub.mp hx
    rw [Subgroup.mem_bot, hφ.ker_iff]
    exact hP'C hgP'
  have hPbar : P = barSub H φ P' := by
    rw [hP'def]
    exact (barSub_barPre hφ P).symm
  rw [hPbar, hbarP']

theorem K1In.of_faithful_action {Y : Type} [Group Y] {E : Type} [Group E]
    (hcomm : ∀ x y : E, x * y = y * x) (hE : ∀ e : E, e * e = 1) (ρ : Y →* MulAut E)
    (hρ : Function.Injective ρ) {A : Subgroup Y} (hA : IsElemAbelian 2 A)
    (hfix : ∀ a ∈ A, a ≠ 1 → ∀ e : E, ρ a e = e → ∀ b ∈ A, ρ b e = e) :
    K1In ⊤ A := by
  intro α hαA β hβA hβ1
  by_cases hα1 : α = 1
  · subst hα1
    refine CFSG.Open.IsElemAbelian.mono (CFSG.Open.isElemAbelian_bot 2) ?_
    rw [Subgroup.closure_le]
    rintro γ ⟨x, hx, rfl⟩
    simp
  · set S : Set Y :=
      {γ : Y | ∃ x ∈ (⊤ : Subgroup Y) ⊓ Subgroup.centralizer ({β} : Set Y),
        γ = x * α * x⁻¹} with hSdef
    have hα2 : α * α = 1 := by
      have h := hA.2 α hαA
      rwa [pow_two] at h
    have hE0α : ∀ e : E, ρ α e = e ↔ ρ β e = e := fun e =>
      ⟨fun he => hfix α hαA hα1 e he β hβA, fun he => hfix β hβA hβ1 e he α hαA⟩
    have hgen_sq : ∀ x, x ∈ Subgroup.centralizer ({β} : Set Y) →
        ρ (x * α * x⁻¹) * ρ (x * α * x⁻¹) = 1 := by
      intro x hx
      have hxx : (x * α * x⁻¹) * (x * α * x⁻¹) = 1 := by
        rw [show (x * α * x⁻¹) * (x * α * x⁻¹) = x * (α * α) * x⁻¹ by group, hα2]
        group
      rw [← map_mul, hxx, map_one]
    have hFixChar : ∀ x, x ∈ Subgroup.centralizer ({β} : Set Y) → ∀ u : E,
        ρ (x * α * x⁻¹) u = u ↔ ρ β u = u := by
      intro x hx u
      have hxβ : β * x = x * β :=
        Subgroup.mem_centralizer_iff.mp hx β (Set.mem_singleton β)
      have hcomm_aut : Commute (ρ x) (ρ β) := by
        show ρ x * ρ β = ρ β * ρ x
        rw [← map_mul, ← map_mul, hxβ]
      have h1 : ρ β * (ρ x)⁻¹ = (ρ x)⁻¹ * ρ β :=
        (Commute.inv_right (show Commute (ρ β) (ρ x) from hcomm_aut.symm)).eq
      have hβx : ρ β ((ρ x)⁻¹ u) = (ρ x)⁻¹ (ρ β u) := by
        calc ρ β ((ρ x)⁻¹ u) = (ρ β * (ρ x)⁻¹) u := rfl
          _ = ((ρ x)⁻¹ * ρ β) u := by rw [h1]
          _ = (ρ x)⁻¹ (ρ β u) := rfl
      constructor
      · intro hu
        have h2 : ρ α ((ρ x)⁻¹ u) = (ρ x)⁻¹ u := by
          have hu' : ρ x (ρ α ((ρ x)⁻¹ u)) = u := by
            simpa only [map_mul, map_inv, MulAut.mul_apply] using hu
          have hcong := congrArg (fun z => (ρ x)⁻¹ z) hu'
          simpa using hcong
        have h3 : ρ β ((ρ x)⁻¹ u) = (ρ x)⁻¹ u := (hE0α _).mp h2
        have h4 : (ρ x)⁻¹ (ρ β u) = (ρ x)⁻¹ u := by rw [← hβx, h3]
        exact (MulEquiv.injective (ρ x)⁻¹) h4
      · intro hu
        have h3 : ρ β ((ρ x)⁻¹ u) = (ρ x)⁻¹ u := by rw [hβx, hu]
        have h2 : ρ α ((ρ x)⁻¹ u) = (ρ x)⁻¹ u := (hE0α _).mpr h3
        calc ρ (x * α * x⁻¹) u = ρ x (ρ α ((ρ x)⁻¹ u)) := by
              simp only [map_mul, map_inv, MulAut.mul_apply]
          _ = ρ x ((ρ x)⁻¹ u) := by rw [h2]
          _ = u := by simp
    have huE0 : ∀ x, x ∈ Subgroup.centralizer ({β} : Set Y) → ∀ e : E,
        ρ β (ρ (x * α * x⁻¹) e * e⁻¹) = ρ (x * α * x⁻¹) e * e⁻¹ := by
      intro x hx e
      have hsq : ρ (x * α * x⁻¹) * ρ (x * α * x⁻¹) = 1 := hgen_sq x hx
      have hgu : ρ (x * α * x⁻¹) (ρ (x * α * x⁻¹) e * e⁻¹) =
          ρ (x * α * x⁻¹) e * e⁻¹ := by
        have hcalc : ρ (x * α * x⁻¹) (ρ (x * α * x⁻¹) e * e⁻¹) =
            e * (ρ (x * α * x⁻¹) e)⁻¹ := by
          calc ρ (x * α * x⁻¹) (ρ (x * α * x⁻¹) e * e⁻¹)
              = ρ (x * α * x⁻¹) (ρ (x * α * x⁻¹) e) *
                  ρ (x * α * x⁻¹) (e⁻¹) := map_mul _ _ _
            _ = (ρ (x * α * x⁻¹) * ρ (x * α * x⁻¹)) e *
                  (ρ (x * α * x⁻¹) e)⁻¹ := by
                  simp only [map_inv, MulAut.mul_apply]
            _ = e * (ρ (x * α * x⁻¹) e)⁻¹ := by rw [hsq]; rfl
        rw [hcalc,
          show (ρ (x * α * x⁻¹) e)⁻¹ = ρ (x * α * x⁻¹) e from
            inv_eq_of_mul_eq_one_right (hE _),
          show e⁻¹ = e from inv_eq_of_mul_eq_one_right (hE e)]
        exact hcomm e (ρ (x * α * x⁻¹) e)
      exact (hFixChar x hx _).mp hgu
    have hcomm_gen : ∀ x₁, x₁ ∈ Subgroup.centralizer ({β} : Set Y) → ∀ x₂,
        x₂ ∈ Subgroup.centralizer ({β} : Set Y) →
        ρ (x₁ * α * x₁⁻¹) * ρ (x₂ * α * x₂⁻¹) =
          ρ (x₂ * α * x₂⁻¹) * ρ (x₁ * α * x₁⁻¹) := by
      intro x₁ hx₁ x₂ hx₂
      refine MulEquiv.ext fun e => ?_
      have h2 : ρ β (ρ (x₂ * α * x₂⁻¹) e * e⁻¹) =
          ρ (x₂ * α * x₂⁻¹) e * e⁻¹ := huE0 x₂ hx₂ e
      have hfix1 : ρ (x₁ * α * x₁⁻¹) (ρ (x₂ * α * x₂⁻¹) e * e⁻¹) =
          ρ (x₂ * α * x₂⁻¹) e * e⁻¹ := (hFixChar x₁ hx₁ _).mpr h2
      have hu1 : e * (ρ (x₁ * α * x₁⁻¹) e * e⁻¹) = ρ (x₁ * α * x₁⁻¹) e := by
        rw [← mul_assoc, hcomm e (ρ (x₁ * α * x₁⁻¹) e)]
        group
      have hu2 : e * (ρ (x₂ * α * x₂⁻¹) e * e⁻¹) = ρ (x₂ * α * x₂⁻¹) e := by
        rw [← mul_assoc, hcomm e (ρ (x₂ * α * x₂⁻¹) e)]
        group
      have hfix2u1 : ρ (x₂ * α * x₂⁻¹) (ρ (x₁ * α * x₁⁻¹) e * e⁻¹) =
          ρ (x₁ * α * x₁⁻¹) e * e⁻¹ := (hFixChar x₂ hx₂ _).mpr (huE0 x₁ hx₁ e)
      calc (ρ (x₁ * α * x₁⁻¹) * ρ (x₂ * α * x₂⁻¹)) e
          = ρ (x₁ * α * x₁⁻¹) (ρ (x₂ * α * x₂⁻¹) e) := rfl
        _ = ρ (x₁ * α * x₁⁻¹) (e * (ρ (x₂ * α * x₂⁻¹) e * e⁻¹)) := by rw [hu2]
        _ = ρ (x₁ * α * x₁⁻¹) e * ρ (x₁ * α * x₁⁻¹)
              (ρ (x₂ * α * x₂⁻¹) e * e⁻¹) := map_mul _ _ _
        _ = ρ (x₁ * α * x₁⁻¹) e * (ρ (x₂ * α * x₂⁻¹) e * e⁻¹) := by rw [hfix1]
        _ = e * (ρ (x₁ * α * x₁⁻¹) e * e⁻¹) *
              (ρ (x₂ * α * x₂⁻¹) e * e⁻¹) := by rw [hu1]
        _ = e * ((ρ (x₁ * α * x₁⁻¹) e * e⁻¹) *
              (ρ (x₂ * α * x₂⁻¹) e * e⁻¹)) := by group
        _ = e * ((ρ (x₂ * α * x₂⁻¹) e * e⁻¹) *
              (ρ (x₁ * α * x₁⁻¹) e * e⁻¹)) := by
              rw [hcomm (ρ (x₁ * α * x₁⁻¹) e * e⁻¹) (ρ (x₂ * α * x₂⁻¹) e * e⁻¹)]
        _ = e * (ρ (x₂ * α * x₂⁻¹) e * e⁻¹) *
              (ρ (x₁ * α * x₁⁻¹) e * e⁻¹) := by group
        _ = ρ (x₂ * α * x₂⁻¹) e * (ρ (x₁ * α * x₁⁻¹) e * e⁻¹) := by rw [hu2]
        _ = ρ (x₂ * α * x₂⁻¹) (e * (ρ (x₁ * α * x₁⁻¹) e * e⁻¹)) := by
              rw [show ρ (x₂ * α * x₂⁻¹) (e * (ρ (x₁ * α * x₁⁻¹) e * e⁻¹)) =
                    ρ (x₂ * α * x₂⁻¹) e *
                      ρ (x₂ * α * x₂⁻¹) (ρ (x₁ * α * x₁⁻¹) e * e⁻¹) from
                    map_mul _ _ _,
                  hfix2u1]
        _ = ρ (x₂ * α * x₂⁻¹) (ρ (x₁ * α * x₁⁻¹) e) := by rw [hu1]
        _ = (ρ (x₂ * α * x₂⁻¹) * ρ (x₁ * α * x₁⁻¹)) e := rfl
    have hcommS : S.Pairwise Commute := by
      intro γ₁ hγ₁ γ₂ hγ₂ _
      obtain ⟨x₁, hx₁, rfl⟩ := hγ₁
      obtain ⟨x₂, hx₂, rfl⟩ := hγ₂
      have hc := hcomm_gen x₁ (Subgroup.mem_inf.mp hx₁).2 x₂ (Subgroup.mem_inf.mp hx₂).2
      have hc' : ρ ((x₁ * α * x₁⁻¹) * (x₂ * α * x₂⁻¹)) =
          ρ ((x₂ * α * x₂⁻¹) * (x₁ * α * x₁⁻¹)) := by
        rw [show ρ ((x₁ * α * x₁⁻¹) * (x₂ * α * x₂⁻¹)) =
              ρ (x₁ * α * x₁⁻¹) * ρ (x₂ * α * x₂⁻¹) from map_mul _ _ _,
            show ρ ((x₂ * α * x₂⁻¹) * (x₁ * α * x₁⁻¹)) =
              ρ (x₂ * α * x₂⁻¹) * ρ (x₁ * α * x₁⁻¹) from map_mul _ _ _]
        exact hc
      exact hρ hc'
    have hclosure_comm : IsMulCommutative (Subgroup.closure S) :=
      Subgroup.isMulCommutative_closure hcommS
    have hsq : ∀ g ∈ Subgroup.closure S, g ^ 2 = 1 := by
      intro g hg
      haveI : IsMulCommutative ↥(Subgroup.closure S) := hclosure_comm
      refine Subgroup.closure_induction (p := fun g _ => g ^ 2 = 1) ?_ ?_ ?_ ?_ hg
      · intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        have hyc : y ∈ Subgroup.centralizer ({β} : Set Y) := (Subgroup.mem_inf.mp hy).2
        apply hρ
        rw [map_pow, map_one, pow_two]
        exact hgen_sq y hyc
      · simp
      · intro x y hx hy ihx ihy
        have hxy : Commute x y := by
          have := mul_comm' (⟨x, hx⟩ : ↥(Subgroup.closure S)) ⟨y, hy⟩
          exact Subtype.ext_iff.mp this
        rw [hxy.mul_pow, ihx, ihy, one_mul]
      · intro x hx ih
        rw [inv_pow, ih, inv_one]
    exact ⟨hclosure_comm, hsq⟩

theorem exists_bar_action_eGrp {H T : Subgroup G} {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) :
    ∃ ρ : Q →* MulAut ↥(eGrp H T), Function.Injective ρ ∧
      ∀ (h : ↥H) (e : ↥(eGrp H T)),
        ((ρ (φ h) e : ↥(eGrp H T)) : G) = (h : G) * (e : G) * (h : G)⁻¹ := by
  have hHnorm : H ≤ Subgroup.normalizer (eGrp H T : Set G) :=
    le_normalizer_conjClosure (omegaOneCenterOf T) H
  let ρ₀ : ↥H →* MulAut ↥(eGrp H T) :=
    (Subgroup.normalizerMonoidHom (H := eGrp H T)).comp (Subgroup.inclusion hHnorm)
  have hρ₀apply : ∀ (h : ↥H) (e : ↥(eGrp H T)),
      ((ρ₀ h e : ↥(eGrp H T)) : G) = (h : G) * (e : G) * (h : G)⁻¹ := by
    intro h e
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (eGrp H T)
      (Subgroup.inclusion hHnorm h) e
  have hker0 : ∀ x : ↥H, ρ₀ x = 1 ↔ (x : G) ∈ Subgroup.centralizer (eGrp H T : Set G) := by
    intro x
    constructor
    · intro hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have he : ρ₀ x ⟨y, hy⟩ = ⟨y, hy⟩ := by rw [hx]; rfl
      have hcoe : (x : G) * y * (x : G)⁻¹ = y := by
        have hcong := congrArg (fun z : ↥(eGrp H T) => (z : G)) he
        rwa [hρ₀apply x ⟨y, hy⟩] at hcong
      have hxy : (x : G) * y = y * (x : G) := by
        calc (x : G) * y = ((x : G) * y * (x : G)⁻¹) * (x : G) := by group
          _ = y * (x : G) := by rw [hcoe]
      exact hxy.symm
    · intro hx
      refine MulEquiv.ext fun e => ?_
      apply Subtype.ext
      rw [hρ₀apply x e, MulAut.one_apply]
      have hcomm := Subgroup.mem_centralizer_iff.mp hx (e : G) e.2
      rw [hcomm.symm]
      group
  have hker : MonoidHom.ker ρ₀ = (cGrp H T).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, cGrp, Subgroup.mem_inf]
    exact ⟨fun hx => ⟨x.2, (hker0 x).mp hx⟩, fun hx => (hker0 x).mpr hx.2⟩
  have hkerφ : MonoidHom.ker φ = (cGrp H T).subgroupOf H := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff x
  have hle : MonoidHom.ker φ ≤ MonoidHom.ker ρ₀ := le_of_eq (hkerφ.trans hker.symm)
  let ρ : Q →* MulAut ↥(eGrp H T) :=
    φ.liftOfSurjective hφ.surjective ⟨ρ₀, hle⟩
  have hρφ : ∀ h : ↥H, ρ (φ h) = ρ₀ h := by
    intro h
    exact MonoidHom.liftOfRightInverse_comp_apply
      (f := φ) (f_inv := Function.surjInv hφ.surjective)
      (Function.rightInverse_surjInv hφ.surjective) ⟨ρ₀, hle⟩ h
  refine ⟨ρ, ?_, ?_⟩
  · intro q₁ q₂ hq
    set h₁ := Function.surjInv hφ.surjective q₁ with hh₁
    set h₂ := Function.surjInv hφ.surjective q₂ with hh₂
    have hq₁ : φ h₁ = q₁ := Function.rightInverse_surjInv hφ.surjective q₁
    have hq₂ : φ h₂ = q₂ := Function.rightInverse_surjInv hφ.surjective q₂
    have hρ₀eq : ρ₀ h₁ = ρ₀ h₂ := by
      rw [← hρφ h₁, hq₁, hq, ← hq₂, hρφ h₂]
    have hmem : h₁ * h₂⁻¹ ∈ MonoidHom.ker ρ₀ := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρ₀eq, mul_inv_cancel]
    have hmemφ : h₁ * h₂⁻¹ ∈ MonoidHom.ker φ := by
      rw [hkerφ]
      rwa [hker] at hmem
    have hφeq : φ h₁ = φ h₂ := by
      have h1 := MonoidHom.mem_ker.mp hmemφ
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.mp h1
    calc q₁ = φ h₁ := hq₁.symm
      _ = φ h₂ := hφeq
      _ = q₂ := hq₂
  · intro h e
    rw [hρφ h]
    exact Subgroup.normalizerMonoidHom_apply_apply_coe (eGrp H T)
      (Subgroup.inclusion hHnorm h) e

theorem k1_bar {V H T A : Subgroup G} {i : ℕ} (h : Pre813 V H T i A) {Q : Type} [Group Q]
    {φ : ↥H →* Q} (hφ : IsBarMap H (cGrp H T) φ) : K1In ⊤ (barSub H φ A) := by
  obtain ⟨ρ, hρinj, hρformula⟩ := exists_bar_action_eGrp hφ
  have hH : IsCalH V H := h.calH0.1
  have hEab : IsElemAbelian 2 (eGrp H T) :=
    isElemAbelian_eGrp_of_isCalH hH h.minCex.hyp.sylow
  have hV7 := h.minCex.hyp.hyp7
  obtain ⟨hAT, g₀, hAg₀, -⟩ := h.mem
  have hAab : IsElemAbelian 2 A :=
    CFSG.Open.IsElemAbelian.mono (isElemAbelian_conjSubgroup' hV7.1 g₀) hAg₀
  have hAbar : IsElemAbelian 2 (barSub H φ A) := by
    have h := (hAab.subgroupOf H).map φ
    simpa [barSub] using h
  refine K1In.of_faithful_action ?_ ?_ ρ hρinj hAbar ?_
  · intro x y
    haveI : IsMulCommutative ↥(eGrp H T) := hEab.1
    exact mul_comm' x y
  · intro e
    apply Subtype.ext
    simpa [pow_two] using hEab.2 (e : G) e.2
  · intro abar hbar hbar1 e he bb hbb
    obtain ⟨a, haA, haφ⟩ := mem_barSub.mp hbar
    obtain ⟨b, hbA, hbφ⟩ := mem_barSub.mp hbb
    have ha1 : (a : G) ≠ 1 := by
      intro hh
      have ha_eq : a = 1 := Subtype.ext (by simpa using hh)
      apply hbar1
      rw [← haφ, ha_eq, map_one]
    have hea : (a : G) * (e : G) * (a : G)⁻¹ = (e : G) := by
      have h1 := hρformula a e
      have h2 : ρ (φ a) e = e := by rw [haφ]; exact he
      rw [← h1, h2]
    have hea_cen : (e : G) ∈ Subgroup.centralizer ({(a : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      calc (a : G) * (e : G) = (a : G) * (e : G) * (a : G)⁻¹ * (a : G) := by group
        _ = (e : G) * (a : G) := by rw [hea]
    have hfixeq := (eight_thirteen_faithful hV7 h.calH0 h.minCex.hyp.sylow h.mem h.notLe).2
      (a : G) haA ha1
    have heE : (e : G) ∈ eGrp H T := e.2
    have heA : (e : G) ∈ Subgroup.centralizer (A : Set G) := by
      have hmem : (e : G) ∈ eGrp H T ⊓ Subgroup.centralizer (A : Set G) := by
        rw [hfixeq]
        exact Subgroup.mem_inf.mpr ⟨heE, hea_cen⟩
      exact (Subgroup.mem_inf.mp hmem).2
    apply Subtype.ext
    rw [← hbφ, hρformula b e]
    have hcomm_be := Subgroup.mem_centralizer_iff.mp heA (b : G) hbA
    rw [hcomm_be]
    group

theorem tis_G {V H T A : Subgroup G} {i : ℕ} (h : Pre813 V H T i A) :
    ∀ g ∈ H, A ⊓ conjSubgroup (normalizer (V : Set G)) g = ⊥ ∨
      A ≤ conjSubgroup (normalizer (V : Set G)) g := by
  intro g hg
  have hV7 := h.minCex.hyp.hyp7
  have hV : IsElemAbelian 2 V := hV7.1
  have hTI := hV7.2.2
  have hVne : V ≠ ⊥ := by
    intro hb
    have h2 := hV7.2.1
    rw [hb, Subgroup.card_bot] at h2
    omega
  have hH : IsCalH V H := h.calH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH h.minCex.hyp.sylow
  obtain ⟨hAT, g₀, hAg₀, -⟩ := h.mem
  have hAH : A ≤ H := hAT.trans hTH.le
  have hUt : conjSubgroup V g₀ ⊓ pCoreOf 2 H = ⊥ := by
    rcases eight_four_one hV hTI hVne h.calH0 h.minCex.hyp.sylow g₀ with ⟨-, hn⟩ | ⟨hb, -⟩
    · exfalso
      obtain ⟨x, hx, hxM⟩ := h.notLe
      have hAU : A ≤ conjSubgroup V g₀ ⊓ H := le_inf hAg₀ hAH
      exact hxM ((E3.conjSubgroup_mono_left x hAU).trans (hn x hx))
    · refine eq_bot_iff.mpr fun u hu => ?_
      obtain ⟨huVg, huO⟩ := Subgroup.mem_inf.mp hu
      have hEO := eSub_le_omegaOneCenter hV hH h.minCex.hyp.sylow
      have huC : u ∈ Subgroup.centralizer (eSub V H T : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy =>
          (mem_centralizer_of_mem_omegaOneCenterOf (hEO hy) huO).symm
      have hmem : u ∈ (conjSubgroup V g₀ ⊓ H) ⊓
          Subgroup.centralizer (eSub V H T : Set G) :=
        Subgroup.mem_inf.mpr
          ⟨Subgroup.mem_inf.mpr ⟨huVg, (CFSG.openPCoreOf_le 2 H) huO⟩, huC⟩
      rw [hb] at hmem
      exact hmem
  have hAn : A ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    hAH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H)
  have hUt' : pCoreOf 2 H ⊓ conjSubgroup V g₀ = ⊥ := by rw [inf_comm]; exact hUt
  have hfixO : ∀ a ∈ A, a ≠ 1 →
      pCoreOf 2 H ⊓ Subgroup.centralizer (A : Set G) =
      pCoreOf 2 H ⊓ Subgroup.centralizer ({a} : Set G) :=
    fun a ha ha1 => eight_one (isTI_conj hTI g₀) hAg₀ hAn hUt' ha ha1
  rw [E3.conjSubgroup_normalizer V g]
  set X : Subgroup G := conjSubgroup V g with hXdef
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hne, hnle⟩ := hcon
  have hne' : A ⊓ Subgroup.normalizer (X : Set G) ≠ ⊥ := fun h => hne h
  obtain ⟨b, hb1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne'
  have hbA : (b : G) ∈ A := (Subgroup.mem_inf.mp b.2).1
  have hbN : (b : G) ∈ Subgroup.normalizer (X : Set G) := (Subgroup.mem_inf.mp b.2).2
  have hb1 : (b : G) ≠ 1 := fun hh => hb1' (Subtype.ext hh)
  have hnle' : ¬ (A : Set G) ⊆ (Subgroup.normalizer (X : Set G) : Set G) := hnle
  obtain ⟨a, haA, haN⟩ := Set.not_subset.mp hnle'
  have hXO : X ≤ pCoreOf 2 H := by
    have hgN : g ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) H hg
    calc conjSubgroup V g ≤ conjSubgroup (pCoreOf 2 H) g :=
          E3.conjSubgroup_mono_left g h.calH0.2
      _ = pCoreOf 2 H := conjSubgroup_eq_iff_mem_normalizer.mpr hgN
  have hX2 : IsPGroup 2 X := (isElemAbelian_conjSubgroup' hV g).isPGroup
  have hXne : X ≠ ⊥ := by
    intro hb
    have hcard : Nat.card X = Nat.card V := E3.card_conjSubgroup V g
    rw [hb, Subgroup.card_bot] at hcard
    have h2 := hV7.2.1
    omega
  have hbp2 : IsPGroup 2 (Subgroup.zpowers (b : G)) :=
    hTH.isPGroup.to_le (Subgroup.zpowers_le.mpr (hAT hbA))
  have hbpN : Subgroup.zpowers (b : G) ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr hbN
  have hfixb := inf_centralizer_ne_bot_of_two_groups hbp2 hX2 hbpN hXne
  obtain ⟨y, hy1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hfixb
  have hyX : (y : G) ∈ X := (Subgroup.mem_inf.mp y.2).1
  have hyC : (y : G) ∈ Subgroup.centralizer (Subgroup.zpowers (b : G) : Set G) :=
    (Subgroup.mem_inf.mp y.2).2
  have hy1 : (y : G) ≠ 1 := fun hh => hy1' (Subtype.ext hh)
  have hyO : (y : G) ∈ pCoreOf 2 H := hXO hyX
  have hyb : (y : G) ∈ Subgroup.centralizer ({(b : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Subgroup.mem_centralizer_iff.mp hyC (b : G) (Subgroup.mem_zpowers _)
  have hyA : (y : G) ∈ Subgroup.centralizer (A : Set G) := by
    have h1 : (y : G) ∈ pCoreOf 2 H ⊓ Subgroup.centralizer (A : Set G) := by
      rw [hfixO (b : G) hbA hb1]
      exact Subgroup.mem_inf.mpr ⟨hyO, hyb⟩
    exact (Subgroup.mem_inf.mp h1).2
  have hya : (y : G) ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haA) hyA
  have hcomm_ya : a * (y : G) = (y : G) * a :=
    Subgroup.mem_centralizer_iff.mp hya a (Set.mem_singleton a)
  have hyXa : (y : G) ∈ conjSubgroup X a := by
    rw [mem_conjSubgroup_iff]
    have h2 : a * (y : G) * a⁻¹ = (y : G) := by rw [hcomm_ya]; group
    rw [h2]
    exact hyX
  have hyint : (y : G) ∈ X ⊓ conjSubgroup X a := Subgroup.mem_inf.mpr ⟨hyX, hyXa⟩
  have hTIa := (isTI_conj hTI g) a⁻¹
  rw [t75_conjSubgroup_eq X a⁻¹, inv_inv] at hTIa
  rw [← hXdef] at hTIa
  rcases hTIa with hbot | htop
  · exfalso
    have hmem : (y : G) ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact hyint
    exact hy1 (Subgroup.mem_bot.mp hmem)
  · exfalso
    have hle : X ≤ conjSubgroup X a :=
      calc X = X ⊓ conjSubgroup X a := htop.symm
        _ ≤ conjSubgroup X a := inf_le_right
    have hXY : conjSubgroup X a = X :=
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq (E3.card_conjSubgroup X a))).symm
    exact haN (conjSubgroup_eq_iff_mem_normalizer.mp hXY)

theorem tis_bar (h5_11 : Asch5_11AS) (h5_13 : Asch5_13AS) {V H T A : Subgroup G} {i : ℕ}
    (h : Pre813 V H T i A) {Q : Type} [Group Q] {φ : ↥H →* Q}
    (hφ : IsBarMap H (cGrp H T) φ) :
    ∀ q : Q, barSub H φ A ⊓ conjSubgroup (barSub H φ (H ⊓ normalizer (V : Set G))) q = ⊥ ∨
      barSub H φ A ≤ conjSubgroup (barSub H φ (H ⊓ normalizer (V : Set G))) q := by
  intro q
  obtain ⟨g₁, hg₁⟩ := hφ.surjective q
  have hg : (g₁ : G) ∈ H := g₁.2
  have hH : IsCalH V H := h.calH0.1
  have hTH : IsSylowIn 2 T H := isSylowIn_of_isCalH hH h.minCex.hyp.sylow
  obtain ⟨hAT, g₀, hAg₀, -⟩ := h.mem
  have hAH : A ≤ H := hAT.trans hTH.le
  have hCM : cGrp H T ≤ normalizer (V : Set G) :=
    (cGrp_le_kerMV h5_11 h5_13 h).trans (kerMV_le_normalizer V H)
  have hCH : cGrp H T ≤ H := inf_le_left
  have hCg : cGrp H T ≤ conjSubgroup (normalizer (V : Set G)) (g₁ : G) := by
    intro c hc
    rw [mem_conjSubgroup_iff]
    exact hCM (wc813psa_conj_mem_cGrp hg hc)
  set Y : Subgroup G := H ⊓ conjSubgroup (normalizer (V : Set G)) (g₁ : G) with hYdef
  have hCY : cGrp H T ≤ Y := le_inf hCH hCg
  have hB : conjSubgroup (H ⊓ normalizer (V : Set G)) (g₁ : G) = Y := by
    have hmap : conjSubgroup (H ⊓ normalizer (V : Set G)) (g₁ : G) =
        conjSubgroup H (g₁ : G) ⊓ conjSubgroup (normalizer (V : Set G)) (g₁ : G) := by
      simp only [conjSubgroup]
      exact Subgroup.map_inf_eq _ _ _ (MulAut.conj (g₁ : G)⁻¹).injective
    rw [hmap, hYdef, conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hg)]
  have hconj : conjSubgroup (barSub H φ (H ⊓ normalizer (V : Set G))) q =
      barSub H φ (conjSubgroup (H ⊓ normalizer (V : Set G)) (g₁ : G)) := by
    rw [← hg₁]
    exact wc813psa_conjSubgroup_barSub φ
  rw [hconj, hB]
  rcases tis_G h (g₁ : G) hg with hbot | hle
  · left
    have hinf : barSub H φ A ⊓ barSub H φ Y = barSub H φ (A ⊓ Y) :=
      wc813psa_barSub_inf_of_le hφ hCY
    have hAY : A ⊓ Y = A ⊓ conjSubgroup (normalizer (V : Set G)) (g₁ : G) := by
      rw [hYdef, ← inf_assoc, inf_eq_left.mpr hAH]
    rw [hinf, hAY, hbot]
    simp [barSub]
  · right
    have hAY : A ≤ Y := le_inf hAH hle
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hAY)

end CFSG.LocalAnalysis.WeakClosure81

end
