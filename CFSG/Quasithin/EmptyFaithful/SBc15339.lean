module

public import CFSG.Quasithin.EmptyFaithful.S153I38
public import CFSG.Quasithin.EmptyFaithful.SBc15312
public import CFSG.Quasithin.EmptyFaithful.S153D52

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc

section Generic

variable {G : Type} [Group G]

theorem exists_mul_of_mem_sup' {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : G}
    (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  let P : Subgroup G :=
    { carrier := {x | ∃ a ∈ A, ∃ b ∈ B, a * b = x}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', b * b', B.mul_mem hb hb', ?_⟩
        calc a * a' * (b * b') = a * (a' * b) * b' := by group
          _ = a * (b * a') * b' := by rw [hAB a' ha' b hb]
          _ = a * b * (a' * b') := by group
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
        have h1 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := hAB a⁻¹ (A.inv_mem ha) b⁻¹ (B.inv_mem hb)
        rw [mul_inv_rev, h1] }
  have hle : A ⊔ B ≤ P := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
    (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
  exact hle hx

theorem centralizes_of_mem_inf_left {L L' V A : Subgroup G}
    (hcomm : ∀ l ∈ L, ∀ l' ∈ L', l * l' = l' * l) (hV : V ≤ L ⊔ L')
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hVL : V ⊓ L = ⊥) {a : G} (haA : a ∈ A)
    (haL : a ∈ L) : ∀ v ∈ V, a * v = v * a := by
  intro v hv
  obtain ⟨vL, hvL, vL', hvL', rfl⟩ := exists_mul_of_mem_sup' hcomm (hV hv)
  have h1 : a * vL' = vL' * a := hcomm a haL vL' hvL'
  have h2 : a * (vL * vL') * a⁻¹ * (vL * vL')⁻¹ = (a * vL * a⁻¹) * vL⁻¹ := by
    have : a * (vL * vL') * a⁻¹ = (a * vL * a⁻¹) * vL' := by
      calc a * (vL * vL') * a⁻¹ = a * vL * (vL' * a⁻¹) := by group
        _ = a * vL * (a⁻¹ * vL') := by
          have : vL' * a⁻¹ = a⁻¹ * vL' := by
            rw [mul_inv_eq_iff_eq_mul]
            calc vL' = a⁻¹ * (a * vL') := by group
              _ = a⁻¹ * (vL' * a) := by rw [h1]
              _ = a⁻¹ * vL' * a := by group
          rw [this]
        _ = (a * vL * a⁻¹) * vL' := by group
    rw [this]
    group
  have hmemV : a * (vL * vL') * a⁻¹ * (vL * vL')⁻¹ ∈ V :=
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAV haA) _).mp hv) (V.inv_mem hv)
  have hmemL : a * (vL * vL') * a⁻¹ * (vL * vL')⁻¹ ∈ L := by
    rw [h2]
    exact L.mul_mem (L.mul_mem (L.mul_mem haL hvL) (L.inv_mem haL)) (L.inv_mem hvL)
  have : a * (vL * vL') * a⁻¹ * (vL * vL')⁻¹ ∈ V ⊓ L := ⟨hmemV, hmemL⟩
  rw [hVL, Subgroup.mem_bot] at this
  have e : a * (vL * vL') = (vL * vL') * a := by
    calc a * (vL * vL') = (a * (vL * vL') * a⁻¹ * (vL * vL')⁻¹) * ((vL * vL') * a) := by group
      _ = (vL * vL') * a := by rw [this, one_mul]
  exact e

theorem centralizes_of_mem_centralizer_left {L L' V A : Subgroup G}
    (hcomm : ∀ l ∈ L, ∀ l' ∈ L', l * l' = l' * l) (hV : V ≤ L ⊔ L')
    (hAV : A ≤ Subgroup.normalizer (V : Set G)) (hAL : A ≤ L ⊔ L') (hVL' : V ⊓ L' = ⊥) {c : G}
    (hcA : c ∈ A) (hcC : c ∈ Subgroup.centralizer (L : Set G)) : ∀ v ∈ V, c * v = v * c := by
  intro v hv
  obtain ⟨vL, hvL, vL', hvL', rfl⟩ := exists_mul_of_mem_sup' hcomm (hV hv)
  obtain ⟨cL, hcL, cL', hcL', hcc⟩ := exists_mul_of_mem_sup' hcomm (hAL hcA)
  have hcN : ∀ x ∈ L', c * x * c⁻¹ ∈ L' := by
    intro x hx
    rw [← hcc]
    have : cL * cL' * x * (cL * cL')⁻¹ = cL' * x * cL'⁻¹ := by
      have h1 : cL * (cL' * x * cL'⁻¹) = (cL' * x * cL'⁻¹) * cL :=
        hcomm cL hcL _ (L'.mul_mem (L'.mul_mem hcL' hx) (L'.inv_mem hcL'))
      calc cL * cL' * x * (cL * cL')⁻¹ = cL * (cL' * x * cL'⁻¹) * cL⁻¹ := by group
        _ = (cL' * x * cL'⁻¹) * cL * cL⁻¹ := by rw [h1]
        _ = cL' * x * cL'⁻¹ := by group
    rw [this]
    exact L'.mul_mem (L'.mul_mem hcL' hx) (L'.inv_mem hcL')
  have h1 : c * vL = vL * c := (Subgroup.mem_centralizer_iff.mp hcC vL hvL).symm
  have hmemV : c * (vL * vL') * c⁻¹ * (vL * vL')⁻¹ ∈ V :=
    V.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAV hcA) _).mp hv) (V.inv_mem hv)
  have h2 : c * (vL * vL') * c⁻¹ * (vL * vL')⁻¹ = vL * ((c * vL' * c⁻¹) * vL'⁻¹) * vL⁻¹ := by
    have hc1 : c * vL * c⁻¹ = vL := by
      rw [mul_inv_eq_iff_eq_mul]
      exact h1
    calc c * (vL * vL') * c⁻¹ * (vL * vL')⁻¹ = (c * vL * c⁻¹) * (c * vL' * c⁻¹) * vL'⁻¹ * vL⁻¹ := by
          group
      _ = vL * (c * vL' * c⁻¹) * vL'⁻¹ * vL⁻¹ := by rw [hc1]
      _ = vL * ((c * vL' * c⁻¹) * vL'⁻¹) * vL⁻¹ := by group
  have hmemL' : c * (vL * vL') * c⁻¹ * (vL * vL')⁻¹ ∈ L' := by
    rw [h2]
    have hk : (c * vL' * c⁻¹) * vL'⁻¹ ∈ L' :=
      L'.mul_mem (hcN vL' hvL') (L'.inv_mem hvL')
    have hk' : vL * ((c * vL' * c⁻¹) * vL'⁻¹) * vL⁻¹ = (c * vL' * c⁻¹) * vL'⁻¹ := by
      have := hcomm vL hvL _ hk
      calc vL * ((c * vL' * c⁻¹) * vL'⁻¹) * vL⁻¹
          = (vL * ((c * vL' * c⁻¹) * vL'⁻¹)) * vL⁻¹ := by group
        _ = (((c * vL' * c⁻¹) * vL'⁻¹) * vL) * vL⁻¹ := by rw [this]
        _ = (c * vL' * c⁻¹) * vL'⁻¹ := by group
    rw [hk']
    exact hk
  have : c * (vL * vL') * c⁻¹ * (vL * vL')⁻¹ ∈ V ⊓ L' := ⟨hmemV, hmemL'⟩
  rw [hVL', Subgroup.mem_bot] at this
  calc c * (vL * vL') = (c * (vL * vL') * c⁻¹ * (vL * vL')⁻¹) * ((vL * vL') * c) := by group
    _ = (vL * vL') * c := by rw [this, one_mul]

end Generic

section Main

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

omit [Finite G] in
theorem commutator_le_of_index_two {V W Y : Subgroup G}
    (hidx : (W.subgroupOf V).index = 2) (hYV : Y ≤ Subgroup.normalizer (V : Set G))
    (hYW : Y ≤ Subgroup.normalizer (W : Set G)) : ⁅V, Y⁆ ≤ W := by
  rw [Subgroup.commutator_le]
  intro v hv y hy
  by_cases hvW : v ∈ W
  · have h1 : y * v⁻¹ * y⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hYW hy) _).mp (W.inv_mem hvW)
    have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hvW h1
  · have hu : y * v⁻¹ * y⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hYV hy) _).mp (V.inv_mem hv)
    have huW : y * v⁻¹ * y⁻¹ ∉ W := by
      intro h'
      apply hvW
      have := (Subgroup.mem_normalizer_iff.mp (hYW (Y.inv_mem hy)) _).mp h'
      have e : y⁻¹ * (y * v⁻¹ * y⁻¹) * y⁻¹⁻¹ = v⁻¹ := by group
      rw [e] at this
      simpa using W.inv_mem this
    have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨v, hv⟩)
      (b := ⟨y * v⁻¹ * y⁻¹, hu⟩)).mpr (by
        constructor
        · intro h'
          exact absurd (Subgroup.mem_subgroupOf.mp h') hvW
        · intro h'
          exact absurd (Subgroup.mem_subgroupOf.mp h') huW)
    have e : ⁅v, y⁆ = v * (y * v⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mem_subgroupOf.mp key

theorem index_eq_two_of_card_four {V W : Subgroup G} (hWV : W ≤ V) (hV : Nat.card V = 4)
    (hW1 : W ≠ ⊥) (hWV' : W ≠ V) : (W.subgroupOf V).index = 2 := by
  have h1 : (W.subgroupOf V).index * Nat.card ↥(W.subgroupOf V) = Nat.card V :=
    Subgroup.index_mul_card (W.subgroupOf V)
  have hc : Nat.card ↥(W.subgroupOf V) = Nat.card W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWV).toEquiv
  rw [hc, hV] at h1
  have hd : Nat.card W ∣ 4 := ⟨_, by rw [mul_comm]; exact h1.symm⟩
  have hne1 : Nat.card W ≠ 1 := fun h' => hW1 (Subgroup.card_eq_one.mp h')
  have hne4 : Nat.card W ≠ 4 := by
    intro h4
    exact hWV' (Subgroup.eq_of_le_of_card_ge hWV (by rw [hV, h4]))
  have hW2 : Nat.card W = 2 := by
    have : Nat.card W ∣ 2 ^ 2 := by simpa using hd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp this
    interval_cases k
    · exact absurd (by simpa using hk') hne1
    · simpa using hk'
    · exact absurd (by simpa using hk') hne4
  rw [hW2] at h1
  omega

theorem input15339Diag_holds (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK) :
    Input15339Diag := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hne hYL0 hr1
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have D : Decomp153 T M V₁ V₂ t := hh.decomp
  have hq := hh.hyp.qtfe
  have hLmem : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLmem
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  obtain ⟨s, hs, z, hz, hsz⟩ : ∃ s ∈ Sgp153 T V₁, ∃ z ∈ L, s * z * s⁻¹ ∉ L := by
    by_contra hno
    push Not at hno
    exact hne (le_antisymm (le_conjClosure _ _) (conjClosure_le hno))
  set L' : Subgroup G := L.map (MulAut.conj s).toMonoidHom with hL'
  have hL'c : L' ∈ cComp I := map_conj_mem_cComp hLmem (hSI hs)
  have hL'mem : L' ∈ conjSubgroupsBy I L := ⟨s, hSI hs, rfl⟩
  have hLmem' : L ∈ conjSubgroupsBy I L := ⟨1, I.one_mem, by ext x; simp⟩
  have hLne : L ≠ L' := by
    intro h
    apply hsz
    have : s * z * s⁻¹ ∈ L' := by
      rw [hL', A38.mem_map_conj]
      have e : s⁻¹ * (s * z * s⁻¹) * s = z := by group
      rw [e]
      exact hz
    rwa [← h] at this
  have hNN : ¬ (L.subgroupOf I).Normal := fun hn =>
    hsz (((Subgroup.normal_subgroupOf_iff_le_normalizer hLI).mp hn (hSI hs) z).mp hz)
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 c.inH.1.2 hLmem with hn | ⟨hcard, -⟩
  · exact absurd hn hNN
  obtain ⟨x₁, y₁, hxy, hset⟩ := Set.ncard_eq_two.mp hcard
  have hmem : ∀ K ∈ conjSubgroupsBy I L, K = L ∨ K = L' := by
    intro K hK
    have hK' := hK
    have h1 := hLmem'
    have h2 := hL'mem
    rw [hset] at hK' h1 h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK' h1 h2
    rcases hK' with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first | exact Or.inl h1.symm | exact Or.inr h2.symm | (exfalso; exact hLne (h1.trans h2.symm))
  have hL0 : conjClosure L (Sgp153 T V₁) ≤ L ⊔ L' := by
    refine conjClosure_le fun g hg l hl => ?_
    have hK : L.map (MulAut.conj g).toMonoidHom ∈ conjSubgroupsBy I L := ⟨g, hSI hg, rfl⟩
    have hgl : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
    rcases hmem _ hK with h | h
    · rw [h] at hgl
      exact Subgroup.mem_sup_left hgl
    · rw [h] at hgl
      exact Subgroup.mem_sup_right hgl
  have hcomm0 : ⁅L, L'⁆ = ⊥ := by
    obtain ⟨hc1, -⟩ := lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 c.inH.1.2 hLmem hL'c hLne
    have hcen : pCoreOf 2 L ≤ Subgroup.centralizer (L : Set G) := c.c33.center_eq ▸ inf_le_right
    exact S153D.commutator_eq_bot_of_quasisimple c.c33.quasisimple
      ((hc1.trans inf_le_left).trans hcen)
  have hcomm : ∀ l ∈ L, ∀ l' ∈ L', l * l' = l' * l := by
    intro l hl l' hl'
    have h := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm0 hl
    exact (Subgroup.mem_centralizer_iff.mp h l' hl').symm
  have hYsup : Yp ≤ L ⊔ L' := (hYL0.trans hL0)
  have hYN : Yp ≤ Subgroup.normalizer (L : Set G) := by
    intro y hy
    obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_sup' hcomm (hYsup hy)
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have : l * l' * x * (l * l')⁻¹ = l * x * l⁻¹ := by
      have h1 : l' * x = x * l' := (hcomm x hx l' hl').symm
      calc l * l' * x * (l * l')⁻¹ = l * (l' * x) * l'⁻¹ * l⁻¹ := by group
        _ = l * (x * l') * l'⁻¹ * l⁻¹ := by rw [h1]
        _ = l * x * l⁻¹ := by group
    rw [this]
    exact L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl)
  have hY2Yp : oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) ≤ Yp := by
    rcases hh.cases with hY | ⟨-, hY⟩
    · rw [hY]
      exact (oTwoUpper_le _).trans inf_le_left
    · rw [hY]
  have hYV₂ : Yp ≤ Subgroup.normalizer (V₂ : Set G) :=
    (hh.Yp_le_Y153).trans (hh.hyp.Y153_le_normalizer_V h113 D).2
  have hSV₂ : Sgp153 T V₁ ≤ Subgroup.normalizer (V₂ : Set G) :=
    Hyp153.Sgp153_le_normalizer_V₂ hh.hyp D
  have hV₂S : V₂ ≤ Sgp153 T V₁ := fun v hv => S153D.VZ_le_Sgp153 hh (D.le₂ hv)
  have hcomV₂ : ⁅V₂, oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G))⁆ = V₂ :=
    hh.hyp.commutator_V₂_Yplus h113 D
  set Y₂ : Subgroup G := oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G)) with hY₂
  have hV₂L0 : V₂ ≤ L ⊔ L' := by
    have h1 : ⁅V₂, Y₂⁆ ≤ conjClosure L (Sgp153 T V₁) := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have hyL0 : y ∈ conjClosure L (Sgp153 T V₁) := hYL0 (hY2Yp hy)
      have h2 := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_conjClosure L (Sgp153 T V₁) (hV₂S hv)) y).mp hyL0
      have e : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := by rw [commutatorElement_def]
      rw [e]
      exact Subgroup.mul_mem _ h2 (Subgroup.inv_mem _ hyL0)
    rw [hcomV₂] at h1
    exact h1.trans hL0
  have hV₂4 : Nat.card ↥V₂ = 4 := D.card₂
  have hV₂ne : V₂ ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hV₂4
    omega
  have hVL : V₂ ⊓ L = ⊥ := by
    by_contra hW1
    have hWV : V₂ ⊓ L ≤ V₂ := inf_le_left
    have hWeq : V₂ ⊓ L = V₂ := by
      by_contra hWne
      have hidx := index_eq_two_of_card_four hWV hV₂4 hW1 hWne
      have hYW : Y₂ ≤ Subgroup.normalizer ((V₂ ⊓ L : Subgroup G) : Set G) := fun g hg =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hYV₂ (hY2Yp hg), hYN (hY2Yp hg)⟩
      have h1 := commutator_le_of_index_two hidx (hYV₂.trans' hY2Yp) hYW
      rw [hcomV₂] at h1
      exact hWne (le_antisymm hWV h1)
    have hV₂L : V₂ ≤ L := hWeq ▸ inf_le_right
    have hV₂L' : V₂ ≤ L' := by
      intro v hv
      rw [hL', A38.mem_map_conj]
      have : s⁻¹ * v * s ∈ V₂ := by
        have := (Subgroup.mem_normalizer_iff.mp (hSV₂ (Sgp153 T V₁ |>.inv_mem hs)) v).mp hv
        simpa using this
      exact hV₂L this
    have hcen : ∀ v ∈ V₂, ∀ y ∈ Yp, y * v = v * y := by
      intro v hv y hy
      obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_sup' hcomm (hYsup hy)
      have h1 : l * v = v * l := hcomm l hl v (hV₂L' hv)
      have h2 : l' * v = v * l' := (hcomm v (hV₂L hv) l' hl').symm
      calc l * l' * v = l * (l' * v) := by group
        _ = l * (v * l') := by rw [h2]
        _ = (l * v) * l' := by group
        _ = (v * l) * l' := by rw [h1]
        _ = v * (l * l') := by group
    have hY₂c : Y₂ ≤ Subgroup.centralizer (V₂ : Set G) := fun y hy =>
      Subgroup.mem_centralizer_iff.mpr fun v hv => (hcen v hv y (hY2Yp hy)).symm
    have hbot : ⁅V₂, Y₂⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hY₂c)
    rw [hcomV₂] at hbot
    exact hV₂ne hbot
  have hVL' : V₂ ⊓ L' = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxV, hxL'⟩
    have h1 : s⁻¹ * x * s ∈ V₂ := by
      have := (Subgroup.mem_normalizer_iff.mp (hSV₂ ((Sgp153 T V₁).inv_mem hs)) x).mp hxV
      simpa using this
    have h2 : s⁻¹ * x * s ∈ L := A38.mem_map_conj.mp hxL'
    have h3 : s⁻¹ * x * s ∈ V₂ ⊓ L := ⟨h1, h2⟩
    rw [hVL, Subgroup.mem_bot] at h3
    have : x = 1 := by
      have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
      rw [e, h3]
      group
    rw [this]
    exact Subgroup.one_mem _
  have hstruct := c.facts11.struct_Yp
  have hexp : ∀ y ∈ Yp, Odd (orderOf y) → y ^ 3 = 1 := fun y hy ho =>
    pow_three_of_odd_of_struct hstruct hy ho
  have hinner : InducesInnerModO2153 Yp L := by
    intro y hy
    obtain ⟨l, hl, l', hl', rfl⟩ := exists_mul_of_mem_sup' hcomm (hYsup hy)
    refine ⟨l, hl, fun x hx => ?_⟩
    have : l * l' * x * (l * l')⁻¹ * (l * x * l⁻¹)⁻¹ = 1 := by
      have h1 : l' * x = x * l' := (hcomm x hx l' hl').symm
      calc l * l' * x * (l * l')⁻¹ * (l * x * l⁻¹)⁻¹
          = l * (l' * x) * l'⁻¹ * l⁻¹ * (l * x * l⁻¹)⁻¹ := by group
        _ = l * (x * l') * l'⁻¹ * l⁻¹ * (l * x * l⁻¹)⁻¹ := by rw [h1]
        _ = 1 := by group
    rw [this]
    exact Subgroup.one_mem _
  have hperf : ⁅L, L⁆ = L := hLmem.2.1
  have hcenterless := centerless_of_quasisimple hperf c.c33.quasisimple c.c33.center_eq
  have hne' : oTwoUpper (Yp ⊓ L) ≠ ⊥ :=
    YL153_ne_bot_of_normalizes hh c.inH c.rank hLI hYN c.c34.rank
  have h3dvd : 3 ∣ Nat.card ↥(Yp ⊓ L) :=
    (three_dvd_card_oTwoUpper hexp (inf_le_left : Yp ⊓ L ≤ Yp) hne').trans
      (Subgroup.card_dvd_of_le (oTwoUpper_le _))
  have hcore : Core12 Yp L := ⟨⟨hYN, hcenterless, hinner⟩, hexp, hr1, h3dvd⟩
  have hKeq := centralizerSection_eq_inf_centralizer (Yp := Yp) c.c33.quasisimple c.c33.center_eq
  have hodd : ∀ y ∈ Yp, Odd (orderOf y) → y ∈ Subgroup.centralizer (V₂ : Set G) := by
    intro y hy ho
    obtain ⟨a, ha, c', hc', hao, hco, rfl⟩ := exists_decomp hcore hy ho
    rw [hKeq] at hc'
    have h1 := centralizes_of_mem_inf_left hcomm hV₂L0 hYV₂ hVL ha.1 ha.2
    have h2 := centralizes_of_mem_centralizer_left hcomm hV₂L0 hYV₂ hYsup hVL' hc'.1 hc'.2
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    calc v * (a * c') = (v * a) * c' := by group
      _ = (a * v) * c' := by rw [h1 v hv]
      _ = a * (v * c') := by group
      _ = a * (c' * v) := by rw [h2 v hv]
      _ = (a * c') * v := by group
  have hYc : Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    calc Yp = oTwoUpper Yp := hh.oTwoUpper_eq.symm
      _ ≤ _ := by
        rw [oTwoUpper, Subgroup.closure_le]
        rintro y ⟨hy, ho⟩
        exact hodd y hy ho
  have hY₂c : Y₂ ≤ Subgroup.centralizer (V₂ : Set G) := (hY2Yp).trans hYc
  have hbot : ⁅V₂, Y₂⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hY₂c)
  rw [hcomV₂] at hbot
  exact hV₂ne hbot

end Main

end SBc

end CFSG.Quasithin
