module

public import CFSG.Quasithin.H13.L32A770n
public import CFSG.Quasithin.Background.E3Weak
public import CFSG.Quasithin.H13.L32A764d
public import CFSG.Quasithin.H13.U3L15Core

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem conjSubgroup_eq_conjSub_inv (A : Subgroup G) (g : G) :
    conjSubgroup A g = conjSub g⁻¹ A := by
  ext x
  rw [mem_conjSubgroup_iff, mem_conjSub, inv_inv]

theorem centralizer_le_normalizer_conjSub
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V)
    {g : G} {A : Subgroup G} (hA : A ≤ conjSub g V) (hA4 : Nat.card A = 4) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (conjSub g V : Set G) := by
  intro c hc
  have hF : conjSub g⁻¹ A ≤ V := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have := hA hx
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  have hF4 : Nat.card (conjSub g⁻¹ A) = 4 := by rw [card_conjSub, hA4]
  have hFc : conjSub g⁻¹ A ≤ conjSub (g⁻¹ * c * g) V := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    rw [mem_conjSub]
    have hcx : c * (g * x * g⁻¹) = (g * x * g⁻¹) * c :=
      (Subgroup.mem_centralizer_iff.mp hc _ hx).symm
    have := hA hx
    rw [mem_conjSub] at this
    rw [show (g⁻¹ * c * g)⁻¹ * x * (g⁻¹ * c * g) = g⁻¹ * (c⁻¹ * (g * x * g⁻¹) * c) * g by
      group]
    rw [show c⁻¹ * (g * x * g⁻¹) * c = g * x * g⁻¹ by
      rw [mul_assoc, ← hcx]; group]
    exact this
  have he := h672 _ hF hF4 _ hFc
  refine mem_normalizer_of_forall_conj_mem fun y hy => ?_
  rw [mem_conjSub] at hy ⊢
  have h1 : (g⁻¹ * c * g) * (g⁻¹ * y * g) * (g⁻¹ * c * g)⁻¹ ∈ conjSub (g⁻¹ * c * g) V :=
    mul_mem_conjSub hy
  rw [he] at h1
  rw [show g⁻¹ * (c * y * c⁻¹) * g = (g⁻¹ * c * g) * (g⁻¹ * y * g) * (g⁻¹ * c * g)⁻¹ by group]
  exact h1

omit [Finite G] in
theorem comm_of_le_conjSub (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {g : G}
    (hV1 : fsuV1 T V ≤ conjSub g V) {v w : G} (hv : v ∈ V) (hw : w ∈ conjSub g V) :
    v * w = w * v := by
  have h1 := hF.weak_f g⁻¹ (by rwa [inv_inv])
  rw [inv_inv, Subgroup.commutator_eq_bot_iff_le_centralizer] at h1
  exact (Subgroup.mem_centralizer_iff.mp (h1 hv) w hw).symm

theorem conjSub_le_centralizer_of_le_R1 (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V) {g : G}
    (hg : conjSub g V ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    conjSub g V ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨hVel, hV8, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  set P := conjSub g V with hP
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  have hRT : R ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hTH := T_le_hz h h63
  have hP8 : Nat.card P = 8 := by rw [hP, card_conjSub, hV8]
  have hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    rw [hP, mem_conjSub] at ha hb
    have := F7.isElemAbelian_comm hVel ha hb
    calc a * b = g * ((g⁻¹ * a * g) * (g⁻¹ * b * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * b * g) * (g⁻¹ * a * g)) * g⁻¹ := by rw [this]
      _ = b * a := by group
  intro p hp
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  by_contra hne
  have hφ : ∀ q ∈ P, q * v * q⁻¹ * v⁻¹ ∈ fsuV1 T V := fun q hq =>
    comm_mem_of_R1 hF (hg hq) hv
  have hcen : ∀ q ∈ P, ∀ c ∈ fsuV1 T V, q * c * q⁻¹ = c := fun q hq c hc => by
    have hqH : q ∈ hz T V := hTH (hRT (hg hq))
    rw [← Subgroup.mem_centralizer_iff.mp hqH c hc, mul_inv_cancel_right]
  let φ : ↥P →* ↥(fsuV1 T V) :=
    { toFun := fun q => ⟨q * v * (q : G)⁻¹ * v⁻¹, hφ q q.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        simp only [Subgroup.coe_mul, MulMemClass.mk_mul_mk]
        have e := hcen a a.2 _ (hφ b b.2)
        calc (a : G) * b * v * ((a : G) * b)⁻¹ * v⁻¹ =
            ((a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * (a : G)⁻¹) *
              ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by group
          _ = _ := by
            rw [e]
            exact F7.isElemAbelian_comm hVel ((inf_le_left : fsuV1 T V ≤ V) (hφ b b.2))
              ((inf_le_left : fsuV1 T V ≤ V) (hφ a a.2))) }
  have hφ1 : φ ⟨p, hp⟩ ≠ 1 := by
    intro h1
    have h2 : p * v * p⁻¹ * v⁻¹ = 1 := congrArg Subtype.val h1
    apply hne
    calc v * p = p * v * p⁻¹ * v⁻¹ * (v * p) := by rw [h2, one_mul]
      _ = p * v := by group
  have hsurj : Function.Surjective φ := by
    intro c
    by_cases hc : c = 1
    · exact ⟨1, by rw [hc, map_one]⟩
    · refine ⟨⟨p, hp⟩, ?_⟩
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV1
      rw [hy _ hφ1, hy _ hc]
  set A := (φ.ker).map P.subtype with hA
  have hA4 : Nat.card A = 4 := by
    have e := Subgroup.card_ker_mul_card_range φ
    rw [MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hV1, hP8] at e
    rw [hA, Subgroup.card_map_of_injective P.subtype_injective]
    omega
  have hAP : A ≤ P := Subgroup.map_subtype_le _
  have hvA : v ∈ Subgroup.centralizer (A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨q, hq, rfl⟩
    have h1 : (q : G) * v * (q : G)⁻¹ * v⁻¹ = 1 := congrArg Subtype.val hq
    calc (q : G) * v = (q : G) * v * (q : G)⁻¹ * v⁻¹ * (v * q) := by group
      _ = v * q := by rw [h1, one_mul]
  have hvN := centralizer_le_normalizer_conjSub h672 hAP hA4 hvA
  have hcP : p * v * p⁻¹ * v⁻¹ ∈ P := by
    rw [show p * v * p⁻¹ * v⁻¹ = p * (v * p⁻¹ * v⁻¹) by group]
    exact mul_mem hp ((Subgroup.mem_normalizer_iff.mp hvN _).mp (inv_mem hp))
  have hV1P : fsuV1 T V ≤ P := by
    refine le_of_card_eq_two_of_inf_ne_bot hV1 fun hbot => hφ1 (Subtype.ext ?_)
    have : p * v * p⁻¹ * v⁻¹ ∈ fsuV1 T V ⊓ P := ⟨hφ p hp, hcP⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  exact hne (comm_of_le_conjSub hF hV1P hv hp)

theorem V_le_pCoreOf_LT (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two) : V ≤ pCoreOf 2 (L ⊔ T) :=
  fun _ hv => (U3.mem_reducedAggregate' ((h.hyp1223 h13322).irrPlus.1 hv)).1

theorem pCoreOf_LT_le_R1 (h : Hyp147 G T L V) :
    pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2
    ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)).trans
      le_sup_right)
    ((L₁Of_sup_le L (fsuV1 T V) T).trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem wClos_R1_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V) :
    E3.wClos V 0 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ pCoreOf 2 (L ⊔ T) := by
  obtain ⟨hVel, -, -, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  refine E3.wClos_le_of_forall fun A hA => ?_
  obtain ⟨hAR, g, hAg, hm⟩ := hA
  have hAeq : A = conjSubgroup V g :=
    (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hVel) g)
      hAg).1 hm
  rw [hAeq, conjSubgroup_eq_conjSub_inv] at hAR ⊢
  rw [← hF.cT]
  exact le_inf (hAR.trans hRT) (conjSub_le_centralizer_of_le_R1 h hMod h63 hF h672 hAR)

theorem wClos_R1_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V) :
    E3.wClos V 0 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) = E3.wClos V 0 (pCoreOf 2 (L ⊔ T)) :=
  E3.e3_15 ⟨le_rfl, pCoreOf_isPGroup 2 _, by rw [Subgroup.relIndex_self]; norm_num⟩
    (pCoreOf_LT_le_R1 h) (pCoreOf_isPGroup 2 _) (wClos_R1_le h hMod h63 hF h672)

theorem le_normalizer_wClos_R1 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V) :
    L ⊔ T ≤ Subgroup.normalizer
      (E3.wClos V 0 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : Set G) := by
  rw [wClos_R1_eq h hMod h63 hF h672]
  exact (le_normalizer_pCoreOf 2 _).trans (E3.normalizer_le_normalizer_wClos _)

theorem normalizer_wClos_R1_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h13322 : Stmt13_3_2_two) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V) :
    Subgroup.normalizer (E3.wClos V 0 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  have hVR : V ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    (V_le_pCoreOf_LT h h13322).trans (pCoreOf_LT_le_R1 h)
  have hVW : V ≤ E3.wClos V 0 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :=
    E3.le_wClos ⟨hVR, 1, by rw [conjSubgroup_one], by rw [conjSubgroup_one]; exact E3.mQuot_self V⟩
  have hV1 : V ≠ ⊥ := h.fsu.irrPlus.2.1
  refine normalizer_le_normalizer_L h h13322 (fun hb => hV1 (le_bot_iff.mp (hb ▸ hVW)))
    ((pCoreOf_isPGroup 2 _).to_le (E3.wClos_le 0 _)) (le_normalizer_wClos_R1 h hMod h63 hF h672)

end CFSG.Quasithin.H13.L32A
