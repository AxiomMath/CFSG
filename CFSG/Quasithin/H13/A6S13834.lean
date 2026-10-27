module

public import CFSG.Quasithin.H13.A6S1384b
public import CFSG.Quasithin.H13.A6S1384a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.F7

@[expose] def c234 : Perm (Fin 6) := swap 2 3 * swap 3 4

@[expose] def c345 : Perm (Fin 6) := swap 3 4 * swap 4 5

@[expose] def c012 : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def c123 : Perm (Fin 6) := swap 1 2 * swap 2 3

theorem c3_signs : Perm.sign c234 = 1 ∧ Perm.sign c345 = 1 ∧ Perm.sign c012 = 1 ∧
    Perm.sign c123 = 1 ∧ c234 ^ 3 = 1 ∧ c345 ^ 3 = 1 ∧ c012 ^ 3 = 1 := by
  decide +kernel

theorem c3_facts : c234 ∈ alternatingGroup (Fin 6) ∧ c345 ∈ alternatingGroup (Fin 6) ∧
    c012 ∈ alternatingGroup (Fin 6) ∧ c123 ∈ alternatingGroup (Fin 6) ∧
    c234 ^ 3 = 1 ∧ c345 ^ 3 = 1 ∧ c012 ^ 3 = 1 := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := c3_signs
  exact ⟨Perm.mem_alternatingGroup.mpr h1, Perm.mem_alternatingGroup.mpr h2,
    Perm.mem_alternatingGroup.mpr h3, Perm.mem_alternatingGroup.mpr h4, h5, h6, h7⟩

theorem centralizer_c234_c345 : ∀ x : Perm (Fin 6), c234 * x = x * c234 → c345 * x = x * c345 →
    x * x = 1 → x = 1 ∨ x = swap 0 1 := by
  decide +kernel

theorem normalizer_pair_c234_c345 : ∀ y : Perm (Fin 6), y * swap 0 1 = swap 0 1 * y →
    (c234 * y * c234⁻¹ = y ∨ c234 * y * c234⁻¹ = swap 0 1 * y) →
    (c345 * y * c345⁻¹ = y ∨ c345 * y * c345⁻¹ = swap 0 1 * y) → y = 1 ∨ y = swap 0 1 := by
  decide +kernel

theorem centralizer_c012_c345 : ∀ x : Perm (Fin 6), c012 * x = x * c012 → c345 * x = x * c345 →
    x * x = 1 → x = 1 := by
  decide +kernel

theorem centralizer_alt6 : ∀ m : Perm (Fin 6), m * c012 = c012 * m → m * c123 = c123 * m →
    m * c234 = c234 * m → m * c345 = c345 * m → m = 1 := by
  decide +kernel

@[expose] def NoPair (σ₁ σ₂ : Perm (Fin 6)) : Prop :=
  ∀ x y : Perm (Fin 6), x * x = 1 → x ≠ 1 → y * y = 1 → y ≠ 1 → y ≠ x → x * y = y * x →
    σ₁ * x = x * σ₁ → σ₂ * x = x * σ₂ → (σ₁ * y * σ₁⁻¹ = y ∨ σ₁ * y * σ₁⁻¹ = x * y) →
      (σ₂ * y * σ₂⁻¹ = y ∨ σ₂ * y * σ₂⁻¹ = x * y) → False

theorem noPair_c234_c345 : NoPair c234 c345 := by
  intro x y hx hx1 _ hy1 hyx hxy h1 h2 h3 h4
  rcases centralizer_c234_c345 x h1 h2 hx with rfl | rfl
  · exact hx1 rfl
  · rcases normalizer_pair_c234_c345 y hxy.symm h3 h4 with rfl | rfl
    · exact hy1 rfl
    · exact hyx rfl

theorem noPair_c012_c345 : NoPair c012 c345 := by
  intro x _ hx hx1 _ _ _ _ h1 h2 _ _
  exact hx1 (centralizer_c012_c345 x h1 h2 hx)

theorem noPair_conj {σ₁ σ₂ : Perm (Fin 6)} (h : NoPair σ₁ σ₂) (τ : Perm (Fin 6)) :
    NoPair (τ * σ₁ * τ⁻¹) (τ * σ₂ * τ⁻¹) := by
  intro x y hx hx1 hy hy1 hyx hxy h1 h2 h3 h4
  have key : ∀ a b : Perm (Fin 6), τ⁻¹ * a * τ = τ⁻¹ * b * τ → a = b := by
    intro a b e
    calc a = τ * (τ⁻¹ * a * τ) * τ⁻¹ := by group
      _ = τ * (τ⁻¹ * b * τ) * τ⁻¹ := by rw [e]
      _ = b := by group
  have hcomm : ∀ σ : Perm (Fin 6), τ * σ * τ⁻¹ * x = x * (τ * σ * τ⁻¹) →
      σ * (τ⁻¹ * x * τ) = τ⁻¹ * x * τ * σ := by
    intro σ e
    calc σ * (τ⁻¹ * x * τ) = τ⁻¹ * (τ * σ * τ⁻¹ * x) * τ := by group
      _ = τ⁻¹ * (x * (τ * σ * τ⁻¹)) * τ := by rw [e]
      _ = τ⁻¹ * x * τ * σ := by group
  have hnorm : ∀ σ : Perm (Fin 6), (τ * σ * τ⁻¹ * y * (τ * σ * τ⁻¹)⁻¹ = y ∨
      τ * σ * τ⁻¹ * y * (τ * σ * τ⁻¹)⁻¹ = x * y) →
      (σ * (τ⁻¹ * y * τ) * σ⁻¹ = τ⁻¹ * y * τ ∨
        σ * (τ⁻¹ * y * τ) * σ⁻¹ = τ⁻¹ * x * τ * (τ⁻¹ * y * τ)) := by
    intro σ e
    have e0 : σ * (τ⁻¹ * y * τ) * σ⁻¹ =
        τ⁻¹ * (τ * σ * τ⁻¹ * y * (τ * σ * τ⁻¹)⁻¹) * τ := by group
    rcases e with e | e
    · left
      rw [e0, e]
    · right
      rw [e0, e]
      group
  refine h (τ⁻¹ * x * τ) (τ⁻¹ * y * τ) ?_ ?_ ?_ ?_ ?_ ?_ (hcomm σ₁ h1) (hcomm σ₂ h2)
    (hnorm σ₁ h3) (hnorm σ₂ h4)
  · calc τ⁻¹ * x * τ * (τ⁻¹ * x * τ) = τ⁻¹ * (x * x) * τ := by group
      _ = 1 := by rw [hx]; group
  · intro e
    exact hx1 (key x 1 (by rw [e]; group))
  · calc τ⁻¹ * y * τ * (τ⁻¹ * y * τ) = τ⁻¹ * (y * y) * τ := by group
      _ = 1 := by rw [hy]; group
  · intro e
    exact hy1 (key y 1 (by rw [e]; group))
  · intro e
    exact hyx (key y x e)
  · calc τ⁻¹ * x * τ * (τ⁻¹ * y * τ) = τ⁻¹ * (x * y) * τ := by group
      _ = τ⁻¹ * (y * x) * τ := by rw [hxy]
      _ = τ⁻¹ * y * τ * (τ⁻¹ * x * τ) := by group

theorem exists_relabel : ∀ v : Fin 6 → ZMod 2, ∑ i, v i = 0 → v ≠ 0 → v ≠ (fun _ => 1) →
    ∃ τ : Perm (Fin 6), v (τ 2) = v (τ 3) ∧ v (τ 3) = v (τ 4) ∧ v (τ 4) = v (τ 5) := by
  decide +kernel

theorem fix_c234_c345 : ∀ f : Fin 6 → ZMod 2, f 2 = f 3 → f 3 = f 4 → f 4 = f 5 →
    ∀ j, f ((c234 : Perm (Fin 6))⁻¹ j) = f j ∧ f ((c345 : Perm (Fin 6))⁻¹ j) = f j := by
  decide +kernel

theorem exists_noPair (v : Fin 6 → ZMod 2) (hv : ∑ i, v i = 0) (hv0 : v ≠ 0) :
    ∃ σ₁ σ₂ : Perm (Fin 6), σ₁ ∈ alternatingGroup (Fin 6) ∧ σ₂ ∈ alternatingGroup (Fin 6) ∧
      σ₁ ^ 3 = 1 ∧ σ₂ ^ 3 = 1 ∧ (∀ j, v (σ₁⁻¹ j) = v j) ∧ (∀ j, v (σ₂⁻¹ j) = v j) ∧
      NoPair σ₁ σ₂ := by
  obtain ⟨h234, h345, h012, -, p234, p345, p012⟩ := c3_facts
  by_cases h1 : v = fun _ => 1
  · subst h1
    exact ⟨c012, c345, h012, h345, p012, p345, fun _ => rfl, fun _ => rfl, noPair_c012_c345⟩
  · obtain ⟨τ, e2, e3, e4⟩ := exists_relabel v hv hv0 h1
    have hfix := fix_c234_c345 (fun i => v (τ i)) e2 e3 e4
    have hA : ∀ σ ∈ alternatingGroup (Fin 6), τ * σ * τ⁻¹ ∈ alternatingGroup (Fin 6) :=
      fun σ hσ => (alternatingGroup.normal (α := Fin 6)).conj_mem σ hσ τ
    have hpow : ∀ σ : Perm (Fin 6), σ ^ 3 = 1 → (τ * σ * τ⁻¹) ^ 3 = 1 := by
      intro σ hσ
      rw [conj_pow, hσ]
      group
    refine ⟨τ * c234 * τ⁻¹, τ * c345 * τ⁻¹, hA _ h234, hA _ h345, hpow _ p234, hpow _ p345,
      fun j => ?_, fun j => ?_, noPair_conj noPair_c234_c345 τ⟩
    · have := (hfix (τ⁻¹ j)).1
      have e : τ (τ⁻¹ j) = j := by simp
      have e2 : (τ * c234 * τ⁻¹)⁻¹ j = τ (c234⁻¹ (τ⁻¹ j)) := by
        simp only [mul_inv_rev, inv_inv, Perm.mul_apply]
      rw [e2]
      rw [e] at this
      exact this
    · have := (hfix (τ⁻¹ j)).2
      have e : τ (τ⁻¹ j) = j := by simp
      have e2 : (τ * c345 * τ⁻¹)⁻¹ j = τ (c345⁻¹ (τ⁻¹ j)) := by
        simp only [mul_inv_rev, inv_inv, Perm.mul_apply]
      rw [e2]
      rw [e] at this
      exact this

theorem alt6_le_of_normalized {M : Subgroup (Perm (Fin 6))} (hM : M ≠ ⊥)
    (hN : ∀ σ ∈ alternatingGroup (Fin 6), ∀ m ∈ M, σ * m * σ⁻¹ ∈ M) :
    alternatingGroup (Fin 6) ≤ M := by
  have hs : IsSimpleGroup ↥(alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  set A := alternatingGroup (Fin 6) with hAdef
  have hAn : A.Normal := alternatingGroup.normal
  have hnorm : ((M ⊓ A).subgroupOf A).Normal := by
    refine ⟨fun n hn a => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ⟨hN a a.2 n hn.1, A.mul_mem (A.mul_mem a.2 hn.2) (A.inv_mem a.2)⟩
  rcases hnorm.eq_bot_or_eq_top with h | h
  · exfalso
    obtain ⟨m, hm1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hM)
    apply hm1
    have hc : ∀ a ∈ A, (m : Perm (Fin 6)) * a = a * m := by
      intro a ha
      have h1 : (m : Perm (Fin 6)) * a * (m : Perm (Fin 6))⁻¹ * a⁻¹ ∈ M ⊓ A := by
        refine ⟨?_, A.mul_mem (hAn.conj_mem a ha m) (A.inv_mem ha)⟩
        have e : (m : Perm (Fin 6)) * a * (m : Perm (Fin 6))⁻¹ * a⁻¹ =
            m * (a * (m : Perm (Fin 6))⁻¹ * a⁻¹) := by group
        rw [e]
        exact M.mul_mem m.2 (hN a ha _ (M.inv_mem m.2))
      have h2 : (⟨_, h1.2⟩ : ↥A) ∈ (M ⊓ A).subgroupOf A := Subgroup.mem_subgroupOf.mpr h1
      rw [h, Subgroup.mem_bot] at h2
      have h3 : (m : Perm (Fin 6)) * a * (m : Perm (Fin 6))⁻¹ * a⁻¹ = 1 :=
        congrArg Subtype.val h2
      calc (m : Perm (Fin 6)) * a = (m * a * (m : Perm (Fin 6))⁻¹ * a⁻¹) * a * m := by group
        _ = a * m := by rw [h3, one_mul]
    obtain ⟨-, -, h012, h123, -, -, -⟩ := c3_facts
    obtain ⟨h234, h345, -⟩ := c3_facts
    exact Subtype.ext (centralizer_alt6 m (hc _ h012) (hc _ h123) (hc _ h234) (hc _ h345))
  · intro a ha
    have : (⟨a, ha⟩ : ↥A) ∈ (M ⊓ A).subgroupOf A := by rw [h]; exact Subgroup.mem_top _
    exact (Subgroup.mem_subgroupOf.mp this).1

theorem inv_mul_mem_of_relIndex_two {G : Type} [Group G] {A B : Subgroup G}
    (h : A.relIndex B = 2) {b₁ b₂ : G} (h1 : b₁ ∈ B) (h2 : b₂ ∈ B) (n1 : b₁ ∉ A) (n2 : b₂ ∉ A) :
    b₁⁻¹ * b₂ ∈ A := by
  have hidx : (A.subgroupOf B).index = 2 := h
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨b₁, h1⟩ : ↥B)⁻¹)
    (b := (⟨b₂, h2⟩ : ↥B))).mpr ?_
  · exact Subgroup.mem_subgroupOf.mp key
  · constructor
    · intro hm
      exact absurd (Subgroup.mem_subgroupOf.mp (by simpa using (A.subgroupOf B).inv_mem hm)) n1
    · intro hm
      exact absurd (Subgroup.mem_subgroupOf.mp hm) n2

theorem exists_case13_8_8_two {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}
    (h : HypF98 T V L V₁ Vp H) {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) (hlt : F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G)) :
    ∃ (δ δ' : F8.Geom T L H) (k : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H δ δ' k ∧
      0 < mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) ∧
      mIdx (conjClosure Vp H) (F8.DH Vp V₁ H (k : G)) ≤
        mIdx (F8.Uγ Vp H (k : G)) (F8.Dγ Vp V₁ H (k : G)) ∧
      autOn (tildeOf V₁ (F8.Uγ Vp H (k : G))) (tildeOf V₁ (conjClosure Vp H)) ∈
        @Qset ↥(tildeOf V₁ (conjClosure Vp H))
          (commGroupOfElemAbelian h.toHypF91.isElemAbelian_tilde)
          (autOn (tildeOf V₁ H) (tildeOf V₁ (conjClosure Vp H))) ∧
      ∃ c ∈ H, conjSub c (F8.Uγ V H (k : G)) ≤ pCoreOf 2 (L₁Of L V₁ ⊔ T) := by
  obtain ⟨δ, δ', k, sk, hpos, hle, hQ⟩ := h.F916_4 s hlt
  refine ⟨δ, δ', k, sk, hpos, hle, hQ, ?_⟩
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ H) (L ⊔ T) H V := h.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic h.amalgamHypV.gen sk.critical.geodesic (by omega : 2 ≤ _)
  have hV2 := (h.F913_2 sk).2 γ₂ hγ₂nb hd
  obtain ⟨c, hc, hcγ⟩ := stab_transitive_on_nbrs hγ₂nb
    (show F8.γ₀ T L H ∈ nbrs (F8.γ₁ T L H) from (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ H)).symm)
  have hcH : (c : G) ∈ H := by rwa [stab_γ₁ h.amalgamHypV.le₂] at hc
  have hc1 : c • F8.γ₁ T L H = F8.γ₁ T L H := smul_eq_of_mem_stab hc
  refine ⟨c, hcH, ?_⟩
  have h1 := conjSub_mono (c : G) hV2
  rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hc1, hcγ, inf_comm,
    h.F913_1] at h1
  exact h1

theorem DH_lt_of_forall {G : Type} [Group G] [Finite G] {T V L V₁ Vp H : Subgroup G}
    (h : HypF98 T V L V₁ Vp H)
    (hall : ∀ (γ γ' : F8.Geom T L H) (g : ↥((L ⊔ T) ⊔ H)), F8Setup T V L H γ γ' g →
      F8.Dγ Vp V₁ H (g : G) < F8.Uγ Vp H (g : G))
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g) :
    F8.DH Vp V₁ H (g : G) < conjClosure Vp H := by
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun hDH => ?_
  obtain ⟨δ, δ', k, y, sk, -, -, eU, -, -, eDγ⟩ :=
    h.exists_symmetric_setup s (h.not_Vγ_le_ballStab_of_lt s (hall γ γ' g s))
  have := hall δ δ' k sk
  rw [eDγ, hDH, ← eU] at this
  exact lt_irrefl _ this

theorem stab_eq_gen_of_struct {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (S : Setting4 G T L V) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    {K : Subgroup G} (hKT : K ⊔ T = S.G1) (ρ : ↥S.G1 →* Perm (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (hKA : ∀ k : ↥S.G1, (k : G) ∈ K → ρ k ∈ alternatingGroup (Fin 6))
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hDH : F8.DH S.V3 (fsuV1 T V) S.G1 (g : G) < conjClosure S.V3 S.G1) :
    stab γ = conjClosure (conjClosure S.V3 S.G1) (stab γ) ⊔ (stab γ ⊓ stab γ') := by
  have hstab : stab γ = conjSub (g : G) S.G1 := S.stab_γ_eq hF s
  have hstab' : stab γ' = conjSub (g : G) (L ⊔ T) := S.stab_γ'_eq hF s
  have hUγ : conjClosure S.V3 S.G1 ≤ stab γ :=
    (conjClosure_mono S.V3_le_V le_rfl).trans ((hF.F913_2 s).1.trans ((pCoreOf_le 2 _).trans
      inf_le_right))
  refine le_antisymm ?_ (sup_le (conjClosure_le fun x hx u hu =>
    (stab γ).mul_mem ((stab γ).mul_mem hx (hUγ hu)) ((stab γ).inv_mem hx)) inf_le_left)
  set F₀ := conjSub (g : G)⁻¹ (conjClosure S.V3 S.G1) with hF₀
  set N := conjClosure F₀ S.G1 with hN
  have hF₀H : F₀ ≤ S.G1 := by
    rw [hF₀, conjSub_le_iff, inv_inv, ← hstab]
    exact hUγ
  have hTH : T ≤ S.G1 := le_sup_right.trans hKT.le
  have hKH : K ≤ S.G1 := le_sup_left.trans hKT.le
  have hQT : pCoreOf 2 S.G1 ≤ T := isSylowTwoOf_pCoreOf_le hF.sylow_H
  have hF₀Q : ¬ F₀ ≤ pCoreOf 2 S.G1 := by
    intro hle
    apply hDH.ne
    refine le_antisymm (centralizerMod_le_left _ _ _) fun u hu => ?_
    have huQ : u ∈ conjSub (g : G) (pCoreOf 2 S.G1) := by
      have := conjSub_mono (g : G) hle
      rw [hF₀, conjSub_inv_conjSub] at this
      exact this hu
    rw [hF.toHypF91.pCoreOf_eq_centralizerMod, conjSub_centralizerMod] at huQ
    exact mem_centralizerMod.mpr ⟨hu, huQ.2.1, huQ.2.2⟩
  obtain ⟨f, hfF, hfQ⟩ := Set.not_subset.mp hF₀Q
  set M := (N.subgroupOf S.G1).map ρ with hM
  have hMne : M ≠ ⊥ := by
    intro hbot
    apply hfQ
    have hfN : (⟨f, hF₀H hfF⟩ : ↥S.G1) ∈ N.subgroupOf S.G1 :=
      Subgroup.mem_subgroupOf.mpr (le_conjClosure F₀ S.G1 hfF)
    have h1 : ρ ⟨f, hF₀H hfF⟩ ∈ M := Subgroup.mem_map_of_mem ρ hfN
    rw [hbot, Subgroup.mem_bot] at h1
    exact (hker _).mp h1
  have hMN : ∀ σ ∈ alternatingGroup (Fin 6), ∀ m ∈ M, σ * m * σ⁻¹ ∈ M := by
    intro σ hσ m hm
    obtain ⟨k, -, rfl⟩ := honto σ hσ
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hm
    refine Subgroup.mem_map.mpr ⟨k * n * k⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure F₀ S.G1 k.2) n).mp hn
  have hAM := alt6_le_of_normalized hMne hMN
  have hKN : K ≤ N ⊔ pCoreOf 2 S.G1 := by
    intro k hk
    obtain ⟨n, hn, hnk⟩ := Subgroup.mem_map.mp (hAM (hKA ⟨k, hKH hk⟩ hk))
    have h1 : ρ (n⁻¹ * ⟨k, hKH hk⟩) = 1 := by rw [map_mul, map_inv, hnk, inv_mul_cancel]
    have h2 : ((n⁻¹ * ⟨k, hKH hk⟩ : ↥S.G1) : G) ∈ pCoreOf 2 S.G1 := (hker _).mp h1
    have e : k = (n : G) * ((n⁻¹ * ⟨k, hKH hk⟩ : ↥S.G1) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hn) h2
  have hHle : S.G1 ≤ N ⊔ (S.G1 ⊓ (L ⊔ T)) := by
    calc S.G1 = K ⊔ T := hKT.symm
      _ ≤ N ⊔ (S.G1 ⊓ (L ⊔ T)) := by
        refine sup_le (hKN.trans (sup_le_sup_left ?_ _))
          (le_sup_of_le_right (le_inf hTH le_sup_right))
        exact le_inf (pCoreOf_le 2 S.G1) (hQT.trans le_sup_right)
  have h2 := conjSub_mono (g : G) hHle
  rw [conjSub_sup, conjSub_inf, hN, conjSub_conjClosure_eq, hF₀, conjSub_inv_conjSub, ← hstab,
    ← hstab'] at h2
  exact h2

@[expose] def UHCoords {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (S : Setting4 G T L V) (ρ : ↥S.G1 →* Perm (Fin 6)) : Prop :=
  (∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative (AltHeart 6),
      Function.Surjective β ∧
      (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
      ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
        ∀ x : ↥(evenWeight 6), (QuotientAddGroup.mk x : AltHeart 6) =
          Multiplicative.toAdd (β u) →
          (QuotientAddGroup.mk (permWeight 6 (ρ h) x) : AltHeart 6) =
            Multiplicative.toAdd (β v)) ∨
    (∃ β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6),
      Function.Surjective β ∧
      (∀ u : ↥(conjClosure S.V3 S.G1), β u = 1 ↔ (u : G) ∈ fsuV1 T V) ∧
      ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
        Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))

theorem exists_noPair_fixing {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (S : Setting4 G T L V) (ρ : ↥S.G1 →* Perm (Fin 6)) {a : G}
    (ha : a ∈ conjClosure S.V3 S.G1) (haV : a ∉ fsuV1 T V) (hβ : UHCoords S ρ) :
    ∃ σ₁ σ₂ : Perm (Fin 6), σ₁ ∈ alternatingGroup (Fin 6) ∧ σ₂ ∈ alternatingGroup (Fin 6) ∧
      σ₁ ^ 3 = 1 ∧ σ₂ ^ 3 = 1 ∧ NoPair σ₁ σ₂ ∧
      ∀ k : ↥S.G1, (ρ k = σ₁ ∨ ρ k = σ₂) → (k : G) * a * (k : G)⁻¹ * a⁻¹ ∈ fsuV1 T V := by
  have hkU : ∀ k : ↥S.G1, (k : G) * a * (k : G)⁻¹ ∈ conjClosure S.V3 S.G1 := fun k =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure S.V3 S.G1 k.2) a).mp ha
  have hpw : ∀ (σ : Perm (Fin 6)) (x : ↥(evenWeight 6)),
      (∀ j, (x : Fin 6 → ZMod 2) (σ⁻¹ j) = (x : Fin 6 → ZMod 2) j) → permWeight 6 σ x = x :=
    fun σ x hx => Subtype.ext (funext fun j => hx j)
  rcases hβ with ⟨β, -, hβk, hβe⟩ | ⟨β, -, hβk, hβe⟩
  · obtain ⟨r, hr⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (β ⟨a, ha⟩))
    have hsum : ∑ i, (r : Fin 6 → ZMod 2) i = 0 := by
      have := r.2
      simpa [evenWeight] using this
    have hr0 : (r : Fin 6 → ZMod 2) ≠ 0 := by
      intro h0
      apply haV
      refine (hβk ⟨a, ha⟩).mp (toAdd_eq_zero.mp ?_)
      rw [← hr, QuotientAddGroup.eq_zero_iff]
      intro i j
      rw [h0]
      rfl
    obtain ⟨σ₁, σ₂, h1, h2, h3, h4, hf1, hf2, hnp⟩ := exists_noPair _ hsum hr0
    refine ⟨σ₁, σ₂, h1, h2, h3, h4, hnp, fun k hk => ?_⟩
    have hfix : permWeight 6 (ρ k) r = r := by
      rcases hk with hk | hk
      · rw [hk]; exact hpw _ _ hf1
      · rw [hk]; exact hpw _ _ hf2
    have e := hβe k ⟨a, ha⟩ ⟨_, hkU k⟩ rfl r hr
    rw [hfix, hr] at e
    have e2 : β (⟨_, hkU k⟩ * (⟨a, ha⟩ : ↥(conjClosure S.V3 S.G1))⁻¹) = 1 := by
      rw [map_mul, map_inv, ← Multiplicative.toAdd.injective e, mul_inv_cancel]
    exact (hβk _).mp e2
  · set w := Multiplicative.toAdd (β ⟨a, ha⟩) with hw
    have hsum : ∑ i, (w : Fin 6 → ZMod 2) i = 0 := by
      have := w.2
      simpa [evenWeight] using this
    have hw0 : (w : Fin 6 → ZMod 2) ≠ 0 := by
      intro h0
      apply haV
      refine (hβk ⟨a, ha⟩).mp (toAdd_eq_zero.mp ?_)
      exact Subtype.ext h0
    obtain ⟨σ₁, σ₂, h1, h2, h3, h4, hf1, hf2, hnp⟩ := exists_noPair _ hsum hw0
    refine ⟨σ₁, σ₂, h1, h2, h3, h4, hnp, fun k hk => ?_⟩
    have hfix : permWeight 6 (ρ k) w = w := by
      rcases hk with hk | hk
      · rw [hk]; exact hpw _ _ hf1
      · rw [hk]; exact hpw _ _ hf2
    have e := hβe k ⟨a, ha⟩ ⟨_, hkU k⟩ rfl
    rw [← hw, hfix, hw] at e
    have e2 : β (⟨_, hkU k⟩ * (⟨a, ha⟩ : ↥(conjClosure S.V3 S.G1))⁻¹) = 1 := by
      rw [map_mul, map_inv, Multiplicative.toAdd.injective e, mul_inv_cancel]
    exact (hβk _).mp e2

theorem false_of_pair {G : Type} [Group G] [Finite G] {T L V : Subgroup G}
    (S : Setting4 G T L V) (hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1)
    {γ γ' : F8.Geom T L S.G1} {g : ↥((L ⊔ T) ⊔ S.G1)} (s : F8Setup T V L S.G1 γ γ' g)
    {K : Subgroup G} (ρ : ↥S.G1 →* Perm (Fin 6))
    (hker : ∀ h : ↥S.G1, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 S.G1)
    (honto : ∀ σ ∈ alternatingGroup (Fin 6), ∃ k : ↥S.G1, (k : G) ∈ K ∧ ρ k = σ)
    (hβ : UHCoords S ρ) (hA1 : F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1)
    (h1 : mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) = 1)
    (hV2 : mIdx (F8.Uγ V S.G1 (g : G)) (F8.Uγ V S.G1 (g : G) ⊓ pCoreOf 2 S.G1) ≤ 2)
    (h11 : ¬ F8.Uγ V S.G1 (g : G) ≤ F8.Uγ S.V3 S.G1 (g : G) ⊔ pCoreOf 2 S.G1) : False := by
  set Q := pCoreOf 2 S.G1 with hQdef
  set Uγ := F8.Uγ S.V3 S.G1 (g : G) with hUγdef
  set Vγ := F8.Uγ V S.G1 (g : G) with hVγdef
  set a := (g : G) * S.z * (g : G)⁻¹ with ha_def
  have haA : a ∈ F8.A₁ (fsuV1 T V) (g : G) := mul_mem_conjSub (S.mem_V1_iff.mpr (Or.inr rfl))
  have ha1 : a ≠ 1 := by
    intro e
    apply S.z_ne_one
    calc S.z = (g : G)⁻¹ * a * (g : G) := by rw [ha_def]; group
      _ = 1 := by rw [e]; group
  have haV : a ∉ fsuV1 T V := by
    intro h
    have hmem : a ∈ fsuV1 T V ⊓ F8.A₁ (fsuV1 T V) (g : G) := ⟨h, haA⟩
    rw [hF.F913_5b s, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  obtain ⟨σ₁, σ₂, hσ₁, hσ₂, p₁, p₂, hnp, hfix⟩ := exists_noPair_fixing S ρ (hA1 haA) haV hβ
  have hUH : Uγ ≤ S.G1 := hF.Uγ_le_H s
  have hVH : Vγ ≤ S.G1 := hF.Vγ_le_H s
  have hUV : Uγ ≤ Vγ := hF.Uγ_le_Vγ
  have hUab : IsElemAbelian 2 Uγ := hF.isElemAbelian_Uγ
  have hVab : IsElemAbelian 2 Vγ := hF.isElemAbelian_Vγ
  have hstab : stab γ = conjSub (g : G) S.G1 := S.stab_γ_eq hF s
  have hNU : stab γ ≤ Subgroup.normalizer (Uγ : Set G) := HypF98.stab_le_normalizer_Uγ s hF S.V3
  have hNV : stab γ ≤ Subgroup.normalizer (Vγ : Set G) := HypF98.stab_le_normalizer_Uγ s hF V
  have hQn : ∀ h ∈ S.G1, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 S.G1 hh) q).mp hq
  have hUQ : Uγ ≤ Subgroup.normalizer (Q : Set G) := hUH.trans (le_normalizer_pCoreOf 2 S.G1)
  have hrelU : (Uγ ⊓ Q).relIndex Uγ = 2 := by
    have := HypF98.relIndex_eq_two_pow_mIdx (Y := F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G))
      (isPGroup_of_isElemAbelian hUab)
    rw [h1, hF.Dγ_eq_inf_pCoreOf s] at this
    simpa using this
  obtain ⟨u₀, hu₀U, hu₀Q⟩ : ∃ u₀ ∈ Uγ, u₀ ∉ Q := by
    by_contra hall
    push Not at hall
    have : (Uγ ⊓ Q).relIndex Uγ = 1 :=
      Subgroup.relIndex_eq_one.mpr fun x hx => ⟨hx, hall x hx⟩
    omega
  obtain ⟨v₀, hv₀V, hv₀R⟩ := Set.not_subset.mp h11
  set R := (Uγ ⊔ Q) ⊓ Vγ with hRdef
  set W := Vγ ⊓ Q with hWdef
  have hWR : W ≤ R := fun x hx => ⟨Subgroup.mem_sup_right hx.2, hx.1⟩
  have hRV : R ≤ Vγ := inf_le_right
  have hrelW : W.relIndex Vγ ≤ 4 := by
    have := HypF98.relIndex_eq_two_pow_mIdx (Y := W) (isPGroup_of_isElemAbelian hVab)
    rw [this]
    calc 2 ^ mIdx Vγ W ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hV2
      _ = 4 := by norm_num
  have hWR2 : 2 ≤ W.relIndex R := by
    have hne : W.relIndex R ≠ 1 := fun e =>
      hu₀Q ((Subgroup.relIndex_eq_one.mp e ⟨Subgroup.mem_sup_left hu₀U, hUV hu₀U⟩).2)
    have h0 := relIndex_ne_zero' W R
    omega
  have hRV2 : 2 ≤ R.relIndex Vγ := by
    have hne : R.relIndex Vγ ≠ 1 := fun e => hv₀R (Subgroup.relIndex_eq_one.mp e hv₀V).1
    have h0 := relIndex_ne_zero' R Vγ
    omega
  have hrelR : R.relIndex Vγ = 2 := by
    have hmul := Subgroup.relIndex_mul_relIndex W R Vγ hWR hRV
    have : W.relIndex R * R.relIndex Vγ ≤ 4 := hmul ▸ hrelW
    nlinarith
  set x := ρ ⟨u₀, hUH hu₀U⟩ with hxdef
  set y := ρ ⟨v₀, hVH hv₀V⟩ with hydef
  have hρU : ∀ u (hu : u ∈ Uγ), ρ ⟨u, hUH hu⟩ = 1 ∨ ρ ⟨u, hUH hu⟩ = x := by
    intro u hu
    by_cases huQ : u ∈ Q
    · exact Or.inl ((hker _).mpr huQ)
    · right
      have hm := inv_mul_mem_of_relIndex_two hrelU hu₀U hu (fun h => hu₀Q h.2) (fun h => huQ h.2)
      have h2 : ρ (⟨u₀, hUH hu₀U⟩⁻¹ * ⟨u, hUH hu⟩) = 1 := (hker _).mpr hm.2
      rw [map_mul, map_inv, inv_mul_eq_one] at h2
      exact h2.symm
  have hdec : ∀ v ∈ (Uγ ⊔ Q : Subgroup G), ∃ u ∈ Uγ, ∃ q ∈ Q, v = u * q := by
    intro v hv
    have hv' : v ∈ ((Uγ ⊔ Q : Subgroup G) : Set G) := hv
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUQ] at hv'
    obtain ⟨u, hu, q, hq, rfl⟩ := Set.mem_mul.mp hv'
    exact ⟨u, hu, q, hq, rfl⟩
  have hx2 : x * x = 1 := by
    have e : (⟨u₀, hUH hu₀U⟩ : ↥S.G1) * ⟨u₀, hUH hu₀U⟩ = 1 :=
      Subtype.ext (by simpa [pow_two] using hUab.2 u₀ hu₀U)
    rw [hxdef, ← map_mul, e, map_one]
  have hx1 : x ≠ 1 := fun e => hu₀Q ((hker _).mp e)
  have hv₀Q : v₀ ∉ Q := fun h => hv₀R (Subgroup.mem_sup_right h)
  have hy2 : y * y = 1 := by
    have e : (⟨v₀, hVH hv₀V⟩ : ↥S.G1) * ⟨v₀, hVH hv₀V⟩ = 1 :=
      Subtype.ext (by simpa [pow_two] using hVab.2 v₀ hv₀V)
    rw [hydef, ← map_mul, e, map_one]
  have hy1 : y ≠ 1 := fun e => hv₀Q ((hker _).mp e)
  have hyx : y ≠ x := by
    intro e
    have h2 : ρ (⟨u₀, hUH hu₀U⟩⁻¹ * ⟨v₀, hVH hv₀V⟩) = 1 := by
      rw [map_mul, map_inv, ← hxdef, ← hydef, e, inv_mul_cancel]
    have h3 : u₀⁻¹ * v₀ ∈ Q := (hker _).mp h2
    apply hv₀R
    have e2 : v₀ = u₀ * (u₀⁻¹ * v₀) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup hu₀U h3
  have hxy : x * y = y * x := by
    have e : (⟨u₀, hUH hu₀U⟩ : ↥S.G1) * ⟨v₀, hVH hv₀V⟩ = ⟨v₀, hVH hv₀V⟩ * ⟨u₀, hUH hu₀U⟩ :=
      Subtype.ext (isElemAbelian_comm hVab (hUV hu₀U) hv₀V)
    rw [hxdef, hydef, ← map_mul, e, map_mul]
  have hz2 : S.z * S.z = 1 := by
    have := S.z_sq
    rwa [pow_two] at this
  have hsq : ∀ k : ↥S.G1, (k : G) * a * (k : G)⁻¹ * a⁻¹ ∈ fsuV1 T V →
      (k : G) * k * a = a * ((k : G) * k) := by
    intro k hk
    have hkz : (k : G) * S.z = S.z * k := Subgroup.mem_centralizer_singleton_iff.mp k.2
    rcases S.mem_V1_iff.mp hk with h | h
    · have e : (k : G) * a = a * k := by
        calc (k : G) * a = ((k : G) * a * (k : G)⁻¹ * a⁻¹) * a * k := by group
          _ = a * k := by rw [h]; group
      calc (k : G) * k * a = k * (k * a) := by group
        _ = k * (a * k) := by rw [e]
        _ = (k * a) * k := by group
        _ = a * k * k := by rw [e]
        _ = a * (k * k) := by group
    · have e : (k : G) * a = S.z * a * k := by
        calc (k : G) * a = ((k : G) * a * (k : G)⁻¹ * a⁻¹) * a * k := by group
          _ = S.z * a * k := by rw [h]
      calc (k : G) * k * a = k * (k * a) := by group
        _ = k * (S.z * a * k) := by rw [e]
        _ = (k * S.z) * a * k := by group
        _ = (S.z * k) * a * k := by rw [hkz]
        _ = S.z * (k * a) * k := by group
        _ = S.z * (S.z * a * k) * k := by rw [e]
        _ = (S.z * S.z) * a * (k * k) := by group
        _ = a * (k * k) := by rw [hz2]; group
  have hCa : ∀ c : G, c * a = a * c → c ∈ stab γ := by
    intro c hc
    rw [hstab, mem_conjSub]
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc (g : G)⁻¹ * c * (g : G) * S.z = (g : G)⁻¹ * (c * a) * (g : G) := by rw [ha_def]; group
      _ = (g : G)⁻¹ * (a * c) * (g : G) := by rw [hc]
      _ = S.z * ((g : G)⁻¹ * c * (g : G)) := by rw [ha_def]; group
  have hcond : ∀ σ ∈ alternatingGroup (Fin 6), σ ^ 3 = 1 → (σ = σ₁ ∨ σ = σ₂) →
      σ * x = x * σ ∧ (σ * y * σ⁻¹ = y ∨ σ * y * σ⁻¹ = x * y) := by
    intro σ hσ hσ3 hσσ
    obtain ⟨k, -, hk⟩ := honto σ hσ
    have hk2 := hsq k (hfix k (by rw [hk]; exact hσσ))
    set k₄ : ↥S.G1 := k * k * (k * k) with hk₄
    have hk₄a : (k₄ : G) * a = a * k₄ := by
      have e : (k₄ : G) = ((k : G) * k) * ((k : G) * k) := rfl
      rw [e]
      calc (k : G) * k * (k * k) * a = (k * k) * ((k * k) * a) := by group
        _ = (k * k) * (a * (k * k)) := by rw [hk2]
        _ = ((k * k) * a) * (k * k) := by group
        _ = (a * (k * k)) * (k * k) := by rw [hk2]
        _ = a * ((k * k) * (k * k)) := by group
    have hρk₄ : ρ k₄ = σ := by
      rw [hk₄, map_mul, map_mul, hk]
      calc σ * σ * (σ * σ) = σ ^ 3 * σ := by rw [pow_three]; simp only [mul_assoc]
        _ = σ := by rw [hσ3, one_mul]
    have hk₄γ := hCa _ hk₄a
    have hk₄H : (k₄ : G) ∈ S.G1 := k₄.2
    have hu' : (k₄ : G) * u₀ * (k₄ : G)⁻¹ ∈ Uγ :=
      (Subgroup.mem_normalizer_iff.mp (hNU hk₄γ) u₀).mp hu₀U
    have hu'Q : (k₄ : G) * u₀ * (k₄ : G)⁻¹ ∉ Q := by
      intro h
      apply hu₀Q
      have := hQn _ (S.G1.inv_mem hk₄H) _ h
      have e : (k₄ : G)⁻¹ * ((k₄ : G) * u₀ * (k₄ : G)⁻¹) * (k₄ : G)⁻¹⁻¹ = u₀ := by group
      rwa [e] at this
    have hx' : σ * x * σ⁻¹ = x := by
      rcases hρU _ hu' with h | h
      · exfalso
        exact hu'Q ((hker _).mp h)
      · have e : σ * x * σ⁻¹ = ρ ⟨(k₄ : G) * u₀ * (k₄ : G)⁻¹, hUH hu'⟩ := by
          rw [← hρk₄, hxdef, ← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e, h]
    refine ⟨?_, ?_⟩
    · calc σ * x = (σ * x * σ⁻¹) * σ := by group
        _ = x * σ := by rw [hx']
    ·
      have hv' : (k₄ : G) * v₀ * (k₄ : G)⁻¹ ∈ Vγ :=
        (Subgroup.mem_normalizer_iff.mp (hNV hk₄γ) v₀).mp hv₀V
      have hv'R : (k₄ : G) * v₀ * (k₄ : G)⁻¹ ∉ R := by
        intro h
        apply hv₀R
        obtain ⟨u, hu, q, hq, e⟩ := hdec _ h.1
        have e2 : v₀ = ((k₄ : G)⁻¹ * u * (k₄ : G)) * ((k₄ : G)⁻¹ * q * (k₄ : G)) := by
          calc v₀ = (k₄ : G)⁻¹ * ((k₄ : G) * v₀ * (k₄ : G)⁻¹) * (k₄ : G) := by group
            _ = (k₄ : G)⁻¹ * (u * q) * (k₄ : G) := by rw [e]
            _ = _ := by group
        rw [e2]
        refine Subgroup.mul_mem_sup ?_ ?_
        · have h3 := (Subgroup.mem_normalizer_iff.mp (hNU ((stab γ).inv_mem hk₄γ)) u).mp hu
          simpa using h3
        · have h3 := hQn _ (S.G1.inv_mem hk₄H) q hq
          simpa using h3
      have hm := inv_mul_mem_of_relIndex_two hrelR hv₀V hv' (fun h => hv₀R h.1) hv'R
      obtain ⟨u, hu, q, hq, e⟩ := hdec _ hm.1
      have hρm : ρ (⟨v₀, hVH hv₀V⟩⁻¹ * ⟨_, hVH hv'⟩) = ρ ⟨u, hUH hu⟩ := by
        have e2 : (⟨v₀, hVH hv₀V⟩⁻¹ * ⟨_, hVH hv'⟩ : ↥S.G1) =
            ⟨u, hUH hu⟩ * ⟨q, pCoreOf_le 2 S.G1 hq⟩ := Subtype.ext e
        rw [e2, map_mul, (hker ⟨q, pCoreOf_le 2 S.G1 hq⟩).mpr hq, mul_one]
      have hσy : σ * y * σ⁻¹ = ρ ⟨_, hVH hv'⟩ := by
        rw [← hρk₄, hydef, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [map_mul, map_inv, ← hydef] at hρm
      rcases hρU u hu with h | h
      · left
        rw [hσy]
        rw [h, inv_mul_eq_one] at hρm
        exact hρm.symm
      · right
        rw [hσy]
        rw [h, inv_mul_eq_iff_eq_mul] at hρm
        rw [hρm, ← hxy]
  obtain ⟨c1, d1⟩ := hcond σ₁ hσ₁ p₁ (Or.inl rfl)
  obtain ⟨c2, d2⟩ := hcond σ₂ hσ₂ p₂ (Or.inr rfl)
  exact hnp x y hx2 hx1 hy2 hy1 hyx hxy c1 c2 d1 d2

@[expose] def Lemma13834Six : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
    ¬ LieModel G .PSp 3 2 1 → ¬ LieModel G .PSU 4 3 1 → S.G1 ∈ S.Hz →
    IsMulCommutative ↥(conjClosure V S.G1) → ∀ hF : HypF98 T V L (fsuV1 T V) S.V3 S.G1,
      S.Struct13827 → ¬ IsHatA6 L →
      (∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G) < F8.Uγ S.V3 S.G1 (g : G)) →
      ∀ (γ γ' : F8.Geom T L S.G1) (g : ↥((L ⊔ T) ⊔ S.G1)), F8Setup T V L S.G1 γ γ' g →
        0 < mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) →
        mIdx (conjClosure S.V3 S.G1) (F8.DH S.V3 (fsuV1 T V) S.G1 (g : G)) ≤
          mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) →
        autOn (tildeOf (fsuV1 T V) (F8.Uγ S.V3 S.G1 (g : G)))
            (tildeOf (fsuV1 T V) (conjClosure S.V3 S.G1)) ∈
          @Qset ↥(tildeOf (fsuV1 T V) (conjClosure S.V3 S.G1))
            (commGroupOfElemAbelian hF.toHypF91.isElemAbelian_tilde)
            (autOn (tildeOf (fsuV1 T V) S.G1) (tildeOf (fsuV1 T V) (conjClosure S.V3 S.G1))) →
        ∀ c ∈ S.G1, conjSub c (F8.Uγ V S.G1 (g : G)) ≤ pCoreOf 2 (S.L1 ⊔ T) →
          (F8.A₁ (fsuV1 T V) (g : G) ≤ conjClosure S.V3 S.G1 ∧
            fsuV1 T V ≤ F8.Uγ S.V3 S.G1 (g : G)) ∧
          mIdx (F8.Uγ S.V3 S.G1 (g : G)) (F8.Dγ S.V3 (fsuV1 T V) S.G1 (g : G)) = 1 ∧
          ¬ pCoreOf 2 (S.L1 ⊔ pCoreOf 2 S.G1) ≤
              conjSub c (F8.Uγ V S.G1 (g : G)) ⊔ pCoreOf 2 S.G1 ∧
          mIdx (F8.Uγ V S.G1 (g : G)) (F8.Uγ V S.G1 (g : G) ⊓ pCoreOf 2 S.G1) ≤ 2

theorem input13834Six_of (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h13314 : Stmt13_3_14) (h34 : Lemma13834Six) : Input13834Six := by
  intro G _ _ T L V S hNS hNU hG1 hab hF hst hhat hlt
  obtain ⟨γ₀, γ₀', g₀, s₀⟩ := hF.exists_F8Setup
  obtain ⟨γ, γ', g, s, hpos, hle, hQ, c, hcH, hcV⟩ := exists_case13_8_8_two hF s₀ (hlt _ _ _ s₀)
  obtain ⟨⟨hA1, hV1⟩, h1, -, hV2⟩ :=
    h34 G T L V S hNS hNU hG1 hab hF hst hhat hlt γ γ' g s hpos hle hQ c hcH hcV
  have hDH := DH_lt_of_forall hF hlt s
  obtain ⟨K, -, hKT, -, -, hcase, -⟩ := hst
  rcases hcase with ⟨-, ρ, hker, hKA, honto, hβ⟩ | ⟨hh, -⟩
  · have hgen := stab_eq_gen_of_struct S hF s hKT ρ hker hKA honto hDH
    have h11 := S.lemma13_8_11_one hNS h13315 h1356two hG1 hF h13314 s hgen (Or.inl hV1)
    exact false_of_pair S hF s ρ hker honto hβ hA1 h1 hV2 h11
  · exact hhat hh

end CFSG.Quasithin.H13.A6
