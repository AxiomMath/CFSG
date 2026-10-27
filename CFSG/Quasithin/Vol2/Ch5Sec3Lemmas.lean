module

public import CFSG.Quasithin.Vol2.Ch5Sec3Statements
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
import CFSG.Quasithin.Vol2.Ch5Sec1Thm5114
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Goldschmidt.Steps.Sec87d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G]

@[expose] def F431Hyps (M₁ M₂ : Subgroup G) (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) :
    Prop :=
  (∃ (D : Type) (_ : Group D), LieModel D t m 2 f ∧ IsExtensionOfLieAmalgam D M₁ M₂) ∧
  ((t = .PSp ∨ t = .PSU) →
    Subgroup.normalizer (centerOf (pCoreOf 2 M₁) : Set G) = M₁ ∧
      Subgroup.normalizer (centerOf (pCoreOf 2 M₂) : Set G) = M₂) ∧
  (t = .PSL ∧ m = 3 → ∃ z ∈ centerOf (pCoreOf 2 (M₁ ⊓ M₂)), orderOf z = 2 ∧
    Subgroup.centralizer ({z} : Set G) ≤ M₁) ∧
  (¬ (t = .PSL ∧ m = 3) →
    (∀ z ∈ centerOf (perfectCore M₁), orderOf z = 2 →
      Subgroup.centralizer ({z} : Set G) ≤ M₁) ∧
    ∀ z ∈ centerOf (perfectCore M₂), orderOf z = 2 →
      Subgroup.centralizer ({z} : Set G) ≤ M₂) ∧
  (t = .PSp → (∀ u ∈ centerOf (pCoreOf 2 (M₁ ⊓ M₂)), orderOf u = 2 →
      CharTwo (Subgroup.centralizer ({u} : Set G))) ∧ ¬ 2 ∣ (M₁ ⊓ M₂).index)

@[expose] def F431Rank2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M₁ M₂ : Subgroup G) (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ),
      IsSec53Param t m f →
      F431Hyps M₁ M₂ t m f → LieModel G t m 2 f

@[expose] def Stmt5_3_1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      (quasithinIsLocal T L ∧ quasithinIsLocal T (oTwoUpper H) ∧
        IsUniqueM (L ⊔ T) (sec53M1 L) ∧ IsUniqueM (oTwoUpper H ⊔ T) (sec53M2 H) ∧
        sec53M1 L ≠ sec53M2 H) ∧
      (CharTwo (sec53M1 L) ∧ pCoreOf 2 (sec53M1 L) = pCoreOf 2 L ∧
        CharTwo (sec53M2 H) ∧ pCoreOf 2 (sec53M2 H) = pCoreOf 2 (oTwoUpper H)) ∧
      (Subgroup.normalizer (sec53S T L : Set G) = sec53M12 L H ∧
        sec53M1 L ⊓ Subgroup.normalizer (sec53S T L : Set G) = sec53M12 L H ∧
        sec53M2 H ⊓ Subgroup.normalizer (sec53S T L : Set G) = sec53M12 L H) ∧
      (L ⊔ sec53M12 L H = sec53M1 L ∧ oTwoUpper H ⊔ sec53M12 L H = sec53M2 H)

@[expose] def Stmt5_3_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      ∃ (Y : Type) (_ : Group Y), LieModel Y t m 2 f ∧
        IsExtensionOfLieAmalgam Y (sec53M1 L) (sec53M2 H)

@[expose] def Stmt5_3_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      F431Hyps (sec53M1 L) (sec53M2 H) t m f ∨
      (t = .PSL ∧ m = 3 ∧ ∀ z ∈ sec53ZS T L, orderOf z = 2 →
        ¬ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H)

@[expose] def Stmt5_3_3_facts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n : ℕ)
    (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ), Hyp5_2_4 G T M L V H B D L₂ n →
    IsOfLieType52 M L H B D T t m f →
    IsSec53Param t m f →
      (perfectCore (sec53M1 L) = L ∧ perfectCore (sec53M2 H) = oTwoUpper H ∧
        pCoreOf 2 (sec53M12 L H) = sec53S T L) ∧
      (∀ z ∈ centerOf L, z ≠ 1 → ∀ z' ∈ centerOf L, z' ≠ 1 → ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') ∧
      (∀ z ∈ centerOf (oTwoUpper H), z ≠ 1 → ∀ z' ∈ centerOf (oTwoUpper H), z' ≠ 1 →
        ∃ g ∈ B ⊔ D, g * z * g⁻¹ = z') ∧
      (t = .PSp → ∀ u ∈ sec53ZS T L, orderOf u = 2 → ∃ g ∈ B ⊔ D, g * u * g⁻¹ ∈ centerOf T)

theorem stmt5_3_4_of (h533 : Stmt5_3_3) (h431 : F431Rank2) : Stmt5_3_4 := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  rcases h533 G T M L V H B D L₂ n t m f hyp hty hpar with h | h
  · exact Or.inl (h431 G hyp.simple hyp.nonabelian _ _ t m f hpar h)
  · exact Or.inr h

section Lemma533

theorem conj_mem_centerOf {P : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) (hx : x ∈ centerOf P) :
    g * x * g⁻¹ ∈ centerOf P := by
  obtain ⟨hxP, hxc⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_normalizer_iff] at hg
  refine Subgroup.mem_inf.mpr ⟨(hg x).mp hxP, ?_⟩
  rw [Subgroup.mem_centralizer_iff] at hxc ⊢
  intro h hh
  have hh' : g⁻¹ * h * g ∈ P := (hg (g⁻¹ * h * g)).mpr (by simpa [mul_assoc] using hh)
  have hc := hxc _ hh'
  calc h * (g * x * g⁻¹) = g * ((g⁻¹ * h * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * h * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * h := by group

theorem normalizer_le_normalizer_centerOf (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (centerOf P : Set G) :=
  Subgroup.le_set_normalizer_iff.mpr fun _ hg _ hx => conj_mem_centerOf hg hx

theorem centerOf_ne_bot [Finite G] {P : Subgroup G} (hP : IsPGroup 2 P) (hne : P ≠ ⊥) :
    centerOf P ≠ ⊥ := by
  have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hc := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center P)
  intro h0
  have hzP : ((z : P) : G) ∈ centerOf P := by
    refine Subgroup.mem_inf.mpr ⟨(z : P).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩)
  rw [h0, Subgroup.mem_bot] at hzP
  exact hz (Subtype.ext (Subtype.ext hzP))

theorem le_of_isUniqueM_of_isTwoLocal [Finite G] {X M N : Subgroup G} (hU : IsUniqueM X M)
    (hN : IsTwoLocal N) (hXN : X ≤ N) : N ≤ M := by
  obtain ⟨M', hM', hNM'⟩ := exists_maxTwoLocal_ge hN
  have h1 : M' = M := hU.2 M' ⟨hM', hXN.trans hNM'⟩
  exact h1 ▸ hNM'

theorem normalizer_centerOf_pCoreOf_eq [Finite G] {X M : Subgroup G} (hU : IsUniqueM X M) :
    Subgroup.normalizer (centerOf (pCoreOf 2 M) : Set G) = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : pCoreOf 2 M ≠ ⊥ := pCoreOf_ne_bot_of_isTwoLocal hU.1.1.1
  have hO2 : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hMN : M ≤ Subgroup.normalizer (centerOf (pCoreOf 2 M) : Set G) :=
    (Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M)).trans
        (normalizer_le_normalizer_centerOf _)
  refine le_antisymm (le_of_isUniqueM_of_isTwoLocal hU ⟨_, centerOf_ne_bot hO2 hO,
    hO2.to_le inf_le_left, rfl⟩ (hU.1.2.trans hMN)) hMN

theorem centralizer_le_of_transitive [Finite G] {T L M C : Subgroup G}
    (hT : quasithinIsSylowTwo T) (hU : IsUniqueM (L ⊔ T) M)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hCM : C ≤ M)
    (htr : ∀ z ∈ centerOf L, z ≠ 1 → ∀ z' ∈ centerOf L, z' ≠ 1 → ∃ g ∈ C, g * z * g⁻¹ = z')
    {z : G} (hz : z ∈ centerOf L) (hz2 : orderOf z = 2) :
    Subgroup.centralizer ({z} : Set G) ≤ M := by
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hzsq : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hZ2 : IsPGroup 2 (centerOf L) := by
    intro w
    by_cases hw : (w : G) = 1
    · exact ⟨0, Subtype.ext (by simp [hw])⟩
    · obtain ⟨g, -, hg⟩ := htr z hz hz1 w w.2 hw
      refine ⟨1, Subtype.ext ?_⟩
      simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
      rw [← hg, conj_pow, hzsq, mul_one, mul_inv_cancel]
  have hZn : T ≤ Subgroup.normalizer (centerOf L : Set G) :=
    hTL.trans (normalizer_le_normalizer_centerOf L)
  have hZT : centerOf L ≤ T :=
    (isSylowTwoOf_of_isSylowTwo hT (le_sup_right : T ≤ centerOf L ⊔ T)).le_of_normalizes
      le_sup_left (sup_le Subgroup.le_normalizer hZn) hZ2
  have hZne : centerOf L ≠ ⊥ := fun h0 => by
    have := hz
    rw [h0, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨z₀, hz₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (CFSG.Goldschmidt.Sec8.inf_center_ne_bot' hT.1 hZT hZn hZne)
  obtain ⟨hz₀L, hz₀T⟩ := Subgroup.mem_inf.mp z₀.2
  have hz₀ne : (z₀ : G) ≠ 1 := fun h => hz₀1 (Subtype.ext h)
  have hLT : L ⊔ T ≤ Subgroup.centralizer ({(z₀ : G)} : Set G) := by
    refine sup_le ?_ ?_
    · intro l hl
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz₀L).2) l hl
    · intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz₀T).2) s hs
  have hC0 := centralizer_le_of_isUniqueM hU hZ2 hz₀L hz₀ne hLT
  obtain ⟨g, hgC, hg⟩ := htr _ hz₀L hz₀ne z hz hz1
  have hgM : g ∈ M := hCM hgC
  intro c hc
  rw [Subgroup.mem_centralizer_singleton_iff] at hc
  have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({(z₀ : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h0 : (z₀ : G) = g⁻¹ * z * g := by rw [← hg]; group
    rw [h0]
    calc g⁻¹ * c * g * (g⁻¹ * z * g) = g⁻¹ * (c * z) * g := by group
      _ = g⁻¹ * (z * c) * g := by rw [hc]
      _ = g⁻¹ * z * g * (g⁻¹ * c * g) := by group
  have hcM := hC0 hc'
  have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
  rw [this]
  exact M.mul_mem (M.mul_mem hgM hcM) (M.inv_mem hgM)

theorem charTwo_centralizer_of_conj_mem [Finite G] (hK : quasithinIsQTKECat G) {T : Subgroup G}
    (hT : quasithinIsSylowTwo T) {u g : G} (hu : orderOf u = 2) (hg : g * u * g⁻¹ ∈ centerOf T) :
    CharTwo (Subgroup.centralizer ({u} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T' := T.map ((MulAut.conj g⁻¹ : G ≃* G) : G →* G) with hT'
  have hT's : quasithinIsSylowTwo T' :=
    ⟨hT.1.map _, by rw [hT', Subgroup.index_map_equiv]; exact hT.2⟩
  have hwT : g * u * g⁻¹ ∈ Subgroup.centralizer (T : Set G) := (Subgroup.mem_inf.mp hg).2
  have hT'C : T' ≤ Subgroup.centralizer ({u} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := Subgroup.mem_centralizer_iff.mp hwT y hy
    simp only [MonoidHom.coe_ofClass, MulAut.conj_apply, inv_inv]
    calc g⁻¹ * y * g * u = g⁻¹ * (y * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * y) * g := by rw [hc]
      _ = u * (g⁻¹ * y * g) := by group
  have hu2 : IsPGroup 2 (Subgroup.zpowers u) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hu, pow_one]
  have hCN : Subgroup.centralizer ({u} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
    intro c hc
    have huc : Commute u c := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
    have hc' : c ∈ Subgroup.centralizer ((Subgroup.zpowers u : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      exact (Commute.zpow_left huc k).eq
    exact Subgroup.centralizer_le_normalizer _ hc'
  have hZu : Subgroup.zpowers u ≤ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) hCN hu2
  have hO : pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) ≠ ⊥ := by
    intro h0
    have : u ∈ pCoreOf 2 (Subgroup.centralizer ({u} : Set G)) := hZu (Subgroup.mem_zpowers u)
    rw [h0, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  exact charTwo_of_inH' hK hT's ⟨hT'C, hO⟩

end Lemma533

theorem stmt5_3_3_of (h531 : Stmt5_3_1) (h532 : Stmt5_3_2) (hfacts : Stmt5_3_3_facts) :
    Stmt5_3_3 := by
  intro G _ _ T M L V H B D L₂ n t m f hyp hty hpar
  obtain ⟨⟨-, -, hU1, hU2, -⟩, -, -, -⟩ := h531 G T M L V H B D L₂ n t m f hyp hty hpar
  have hext := h532 G T M L V H B D L₂ n t m f hyp hty hpar
  obtain ⟨⟨hpc1, hpc2, hO12⟩, htr1, htr2, hfus⟩ :=
    hfacts G T M L V H B D L₂ n t m f hyp hty hpar
  have hT1 : T ≤ sec53M1 L := hyp.T_le.trans hyp.normal
  have hT2 : T ≤ sec53M2 H := hyp.hStar.1.1.trans (le_normalizer_oTwoUpper H)
  have hB1 : B ≤ sec53M1 L := hyp.notation59.1.1.trans (inf_le_left.trans hyp.normal)
  have hB2 : B ≤ sec53M2 H :=
    hyp.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hD1 : D ≤ sec53M1 L :=
    hyp.notation59.2.1.1.trans (inf_le_left.trans Subgroup.le_normalizer)
  have hBD1 : B ⊔ D ≤ sec53M1 L := sup_le hB1 hD1
  have hBD2 : B ⊔ D ≤ sec53M2 H := sup_le hB2 hyp.D_le
  have hZS : centerOf (pCoreOf 2 (sec53M1 L ⊓ sec53M2 H)) = sec53ZS T L := by
    rw [show sec53M1 L ⊓ sec53M2 H = sec53M12 L H from rfl, hO12]
  have ha : (t = .PSp ∨ t = .PSU) →
      Subgroup.normalizer (centerOf (pCoreOf 2 (sec53M1 L)) : Set G) = sec53M1 L ∧
        Subgroup.normalizer (centerOf (pCoreOf 2 (sec53M2 H)) : Set G) = sec53M2 H :=
    fun _ => ⟨normalizer_centerOf_pCoreOf_eq hU1, normalizer_centerOf_pCoreOf_eq hU2⟩
  have hb : ¬ (t = .PSL ∧ m = 3) →
      (∀ z ∈ centerOf (perfectCore (sec53M1 L)), orderOf z = 2 →
        Subgroup.centralizer ({z} : Set G) ≤ sec53M1 L) ∧
      ∀ z ∈ centerOf (perfectCore (sec53M2 H)), orderOf z = 2 →
        Subgroup.centralizer ({z} : Set G) ≤ sec53M2 H := by
    intro _
    refine ⟨fun z hz hz2 => ?_, fun z hz hz2 => ?_⟩
    · rw [hpc1] at hz
      exact centralizer_le_of_transitive hyp.sylow hU1 hT1 hBD1 htr1 hz hz2
    · rw [hpc2] at hz
      exact centralizer_le_of_transitive hyp.sylow hU2 hT2 hBD2 htr2 hz hz2
  have hcd : t = .PSp → (∀ u ∈ centerOf (pCoreOf 2 (sec53M1 L ⊓ sec53M2 H)), orderOf u = 2 →
      CharTwo (Subgroup.centralizer ({u} : Set G))) ∧ ¬ 2 ∣ (sec53M1 L ⊓ sec53M2 H).index := by
    intro htp
    refine ⟨fun u hu hu2 => ?_, fun h2 => hyp.sylow.2 (h2.trans
      (Subgroup.index_dvd_of_le (le_inf hT1 hT2)))⟩
    rw [hZS] at hu
    obtain ⟨g, -, hg⟩ := hfus htp u hu hu2
    exact charTwo_centralizer_of_conj_mem hyp.qtke hyp.sylow hu2 hg
  by_cases hL3 : t = .PSL ∧ m = 3
  · by_cases hz : ∃ z ∈ sec53ZS T L, orderOf z = 2 ∧
        Subgroup.centralizer ({z} : Set G) ≤ sec53M1 L
    · refine Or.inl ⟨hext, ha, fun _ => ?_, hb, hcd⟩
      rw [hZS]
      exact hz
    · exact Or.inr ⟨hL3.1, hL3.2, fun z hzS hz2 hle =>
        hz ⟨z, hzS, hz2, hle.trans inf_le_left⟩⟩
  · exact Or.inl ⟨hext, ha, fun h => absurd h hL3, hb, hcd⟩

end CFSG.Quasithin.H13
