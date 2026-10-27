module

public import CFSG.Quasithin.H13.L32A705a
public import CFSG.Quasithin.Background.S1549CAlpha
public import CFSG.Quasithin.EmptyFaithful.S145Facts

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Setting147

variable {T L V H : Subgroup G} {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}

theorem UH_le_R1_conj (hF : HypF98 T V L (fsuV1 T V) V H) (s : F8Setup T V L H γ γ' g)
    {u : G} (hu : u ∈ conjClosure V H) :
    (g : G)⁻¹ * u * g ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have h1 := (hF.F913_2 s).1 hu
  have he : stab γ' ⊓ stab γ = Quasithin.conjSub (g : G) (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [← s.edge₀, ← s.edge₁, stab_smul, stab_smul, ← Quasithin.conjSub_inf, hF.F913_1]
  rw [he, pCoreOf_conjSub, Quasithin.mem_conjSub] at h1
  exact h1

theorem comm_Uγ_l1 (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H)
    (h1332 : Stmt13_3_2) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (s : F8Setup T V L H γ γ' g) :
    ⁅F8.Uγ V H (g : G), l1 T L V⁆ ≤ pCoreOf 2 H := by
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  obtain ⟨c, hcH, hc⟩ := S1549C.exists_alpha hF s
  rw [Subgroup.commutator_le]
  intro w hw l hl
  have hw' : c * w * c⁻¹ ∈ pCoreOf 2 (l1 T L V ⊔ T) :=
    hl1eq ▸ hc (Quasithin.mul_mem_conjSub hw)
  have hl' : c * l * c⁻¹ ∈ l1 T L V := (Subgroup.mem_normalizer_iff.mp (hHL hcH) l).mp hl
  have h1 := Setting147.comm_R1_l1 S h1332 hHL hw' hl'
  have e : ⁅w, l⁆ = c⁻¹ * ((c * w * c⁻¹) * (c * l * c⁻¹) * (c * w * c⁻¹)⁻¹ *
      (c * l * c⁻¹)⁻¹) * c⁻¹⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H (inv_mem hcH)) _).mp h1

theorem comm_UH_lγ (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H)
    (h1332 : Stmt13_3_2) (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G))
    (s : F8Setup T V L H γ γ' g) {x u : G} (hx : x ∈ l1 T L V) (hu : u ∈ conjClosure V H) :
    (g : G)⁻¹ * (((g : G) * x * (g : G)⁻¹) * u * ((g : G) * x * (g : G)⁻¹)⁻¹ * u⁻¹) * g ∈
      pCoreOf 2 H := by
  have hl1eq : L₁Of L (fsuV1 T V) = l1 T L V := oTwoRes_eq_oTwoUpper _
  have hr : (g : G)⁻¹ * u * g ∈ pCoreOf 2 (l1 T L V ⊔ T) := hl1eq ▸ UH_le_R1_conj hF s hu
  have h1 := Setting147.comm_R1_l1 S h1332 hHL hr hx
  have e : (g : G)⁻¹ * (((g : G) * x * (g : G)⁻¹) * u * ((g : G) * x * (g : G)⁻¹)⁻¹ * u⁻¹) * g =
      (((g : G)⁻¹ * u * g) * x * ((g : G)⁻¹ * u * g)⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact inv_mem h1

theorem exists_mem_l1_not_O2 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ x ∈ l1 T L V, x ∉ pCoreOf 2 (l1 T L V) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have h3 := (Hyp147.set14 S.hyp h1222 h1332 h1334 hV2).Lp3
  rw [show L₁Of L (fsuV1 T V) = l1 T L V from oTwoRes_eq_oTwoUpper _] at h3
  by_contra h
  push Not at h
  have hle : l1 T L V ≤ pCoreOf 2 (l1 T L V) := fun x hx => h x hx
  rw [Subgroup.relIndex_eq_one.mpr hle] at h3
  omega

omit [Finite G] in
theorem conj_comm_split (y u w : G) :
    y * (u * w * u⁻¹ * w⁻¹) * y⁻¹ =
      (y * u * y⁻¹ * u⁻¹) * (u * (y * w * y⁻¹) * u⁻¹) * (y * u * y⁻¹ * u⁻¹)⁻¹ *
        (u * (y * w * y⁻¹) * u⁻¹)⁻¹ * (u * (y * w * y⁻¹) * u⁻¹ * (y * w * y⁻¹)⁻¹) := by
  group

theorem false_of_transvection (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) {k x : G} (hx : x ∈ l1 T L V)
    (hxO : x ∉ pCoreOf 2 (l1 T L V))
    (hTN : conjClosure V H ≤
      Subgroup.normalizer (Quasithin.conjSub k (conjClosure V H) : Set G))
    (hTC : ⁅conjClosure V H, Quasithin.conjSub k (conjClosure V H)⁆ = fsuV1 T V)
    (hc : ∀ u ∈ conjClosure V H,
      k⁻¹ * ((k * x * k⁻¹) * u * (k * x * k⁻¹)⁻¹ * u⁻¹) * k ∈ pCoreOf 2 H)
    (hQ : pCoreOf 2 H ≤ centralizerMod (fsuV1 T V) H (conjClosure V H))
    (hVA : fsuV1 T V ⊓ Quasithin.conjSub k (fsuV1 T V) = ⊥) : False := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have : IsMulCommutative ↥V := (hMod G T L V S.hyp.hyp S.hyp.fsu).1.1
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have S14 := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  obtain ⟨z, -, -, hz, hz1, -, -, -, -⟩ := S14.exists_basis
  have hxH : x ∈ H := Setting147.l1H' S hx
  have hcomm : ∀ u ∈ conjClosure V H, ∀ w ∈ Quasithin.conjSub k (conjClosure V H),
      u * w * u⁻¹ * w⁻¹ ∈ fsuV1 T V := fun u hu w hw => by
    have := Subgroup.commutator_mem_commutator hu hw
    rwa [hTC, commutatorElement_def] at this
  have hyU : ∀ t ∈ Quasithin.conjSub k (conjClosure V H),
      k * x * k⁻¹ * t * (k * x * k⁻¹)⁻¹ ∈ Quasithin.conjSub k (conjClosure V H) := by
    intro t ht
    rw [Quasithin.mem_conjSub] at ht ⊢
    rw [show k⁻¹ * (k * x * k⁻¹ * t * (k * x * k⁻¹)⁻¹) * k = x * (k⁻¹ * t * k) * x⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V H hxH) _).mp ht
  have hyA : ∀ a : G, k * x * k⁻¹ * a * (k * x * k⁻¹)⁻¹ ∈ Quasithin.conjSub k (fsuV1 T V) →
      a ∈ Quasithin.conjSub k (fsuV1 T V) := by
    intro a ha
    rw [Quasithin.mem_conjSub] at ha ⊢
    rw [show k⁻¹ * (k * x * k⁻¹ * a * (k * x * k⁻¹)⁻¹) * k = x * (k⁻¹ * a * k) * x⁻¹ by
      group] at ha
    exact (Subgroup.mem_normalizer_iff.mp (S.hz.2.1 hxH) _).mpr ha
  have hcA : ∀ u ∈ conjClosure V H, ∀ t ∈ Quasithin.conjSub k (conjClosure V H),
      (k * x * k⁻¹ * u * (k * x * k⁻¹)⁻¹ * u⁻¹) * t *
        (k * x * k⁻¹ * u * (k * x * k⁻¹)⁻¹ * u⁻¹)⁻¹ * t⁻¹ ∈
        Quasithin.conjSub k (fsuV1 T V) := by
    intro u hu t ht
    rw [Quasithin.mem_conjSub] at ht ⊢
    have h1 := (mem_centralizerMod.mp (hQ (hc u hu))).2.2 _ ht
    convert h1 using 1
    group
  obtain ⟨u, hu, w, hw, huw⟩ : ∃ u ∈ conjClosure V H,
      ∃ w ∈ Quasithin.conjSub k (conjClosure V H), u * w * u⁻¹ * w⁻¹ = z := by
    by_contra h
    push Not at h
    have hle : ⁅conjClosure V H, Quasithin.conjSub k (conjClosure V H)⁆ ≤ ⊥ := by
      rw [Subgroup.commutator_le]
      intro u hu w hw
      rw [commutatorElement_def, Subgroup.mem_bot]
      rcases S14.eq_of_mem_V1 hz hz1 (hcomm u hu w hw) with h1 | h1
      · exact h1
      · exact absurd h1 (h u hu w hw)
    rw [hTC] at hle
    exact hz1 (Subgroup.mem_bot.mp (hle hz))
  have hw' := hyU w hw
  obtain ⟨a, ha, v, hv, he⟩ : ∃ a ∈ Quasithin.conjSub k (fsuV1 T V), ∃ v ∈ fsuV1 T V,
      k * x * k⁻¹ * z * (k * x * k⁻¹)⁻¹ = a * v :=
    ⟨_, hcA u hu _ ((Subgroup.mem_normalizer_iff.mp (hTN hu) _).mp hw'), _,
      hcomm u hu _ hw', by rw [← huw]; exact conj_comm_split _ u w⟩
  have hzA : z ∈ Quasithin.conjSub k (fsuV1 T V) := by
    rcases S14.eq_of_mem_V1 hz hz1 hv with h1 | h1
    · rw [h1, mul_one] at he
      exact hyA z (he ▸ ha)
    · rw [h1] at he
      have hzU : k⁻¹ * z * k ∈ conjClosure V H := by
        have := mul_mem ((Subgroup.mem_normalizer_iff.mp (hTN hu) w).mp hw) (inv_mem hw)
        rw [huw, Quasithin.mem_conjSub] at this
        exact this
      have hfix : x * (k⁻¹ * z * k) * x⁻¹ * (k⁻¹ * z * k)⁻¹ ∈ fsuV1 T V := by
        convert Quasithin.mem_conjSub.mp ha using 1
        calc x * (k⁻¹ * z * k) * x⁻¹ * (k⁻¹ * z * k)⁻¹
            = k⁻¹ * (k * x * k⁻¹ * z * (k * x * k⁻¹)⁻¹) * z⁻¹ * k := by group
          _ = k⁻¹ * (a * z) * z⁻¹ * k := by rw [he]
          _ = k⁻¹ * a * k := by group
      exact Quasithin.mem_conjSub.mpr
        (Setting147.mem_V1_of_fix S h1222 h1332 h1334 hHL hx hxO hzU hfix)
  have hbot : z ∈ (⊥ : Subgroup G) := by
    rw [← hVA]
    exact ⟨hz, hzA⟩
  exact hz1 (Subgroup.mem_bot.mp hbot)

theorem Dγ_lt_Uγ (S : Setting147 G T L V H) (hF : HypF98 T V L (fsuV1 T V) V H)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hHL : H ≤ Subgroup.normalizer (l1 T L V : Set G)) (s : F8Setup T V L H γ γ' g) :
    F8.Dγ V (fsuV1 T V) H (g : G) < F8.Uγ V H (g : G) := by
  obtain ⟨x, hx, hxO⟩ := exists_mem_l1_not_O2 S h1222 h1332 h1334
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hD => ?_
  obtain ⟨hTN, -, hTC⟩ := hF.lemma_14_5_18_one s hD.symm
  exact false_of_transvection S h1222 h1332 h1334 hHL hx hxO hTN hTC
    (fun u hu => comm_UH_lγ S hF h1332 hHL s hx hu) hF.pCoreOf_eq_centralizerMod.le
    (hF.F913_5b s)

end Setting147

end CFSG.Quasithin.H13.L32A
