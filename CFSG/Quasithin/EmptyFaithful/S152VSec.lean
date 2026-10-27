module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.Quasithin.S152V

open scoped commutatorElement

section Descent

variable {M : Type*} [Group M]

theorem normal_pGroup_le_ker [IsSimpleGroup M] (hM : ¬ IsPGroup 2 M) {A : Type*} [Group A] (f : A →* M)
    (hf : Function.Surjective f) {Z : Subgroup A} [Z.Normal] (hZ : IsPGroup 2 Z) : Z ≤ f.ker := by
  have : (Z.map f).Normal := Subgroup.Normal.map ‹_› f hf
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Z.map f) with h | h
  · intro z hz
    have hz' : f z ∈ Z.map f := ⟨z, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at hz'
    exact hz'
  · exfalso
    apply hM
    refine hZ.of_surjective (f.comp Z.subtype) fun m => ?_
    have hm : m ∈ Z.map f := by rw [h]; exact Subgroup.mem_top m
    obtain ⟨z, hz, rfl⟩ := hm
    exact ⟨⟨z, hz⟩, rfl⟩

variable {G : Type*} [Group G]

omit [Group M] in
theorem mem_sup_of_le_normalizer {H N : Subgroup G} (hH : H ≤ Subgroup.normalizer (N : Set G)) {x : G}
    (hx : x ∈ H ⊔ N) : ∃ h ∈ H, ∃ n ∈ N, x = h * n := by
  let S : Subgroup G :=
    { carrier := {x | ∃ h ∈ H, ∃ n ∈ N, x = h * n}
      mul_mem' := by
        rintro _ _ ⟨h₁, hh₁, n₁, hn₁, rfl⟩ ⟨h₂, hh₂, n₂, hn₂, rfl⟩
        refine ⟨h₁ * h₂, H.mul_mem hh₁ hh₂, (h₂⁻¹ * n₁ * h₂) * n₂, N.mul_mem ?_ hn₂, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hH (H.inv_mem hh₂)) n₁).1 hn₁
        simpa using this
      one_mem' := ⟨1, H.one_mem, 1, N.one_mem, by simp⟩
      inv_mem' := by
        rintro _ ⟨h, hh, n, hn, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, h * n⁻¹ * h⁻¹, ?_, by group⟩
        have := (Subgroup.mem_normalizer_iff.1 (hH hh) n⁻¹).1 (N.inv_mem hn)
        exact this }
  have hHS : H ≤ S := fun h hh => ⟨h, hh, 1, N.one_mem, by simp⟩
  have hNS : N ≤ S := fun n hn => ⟨1, H.one_mem, n, hn, by simp⟩
  exact (sup_le hHS hNS) hx

theorem exists_hom_of_normalizes (A' H N : Subgroup G) (hAN : A' ≤ Subgroup.normalizer (N : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (f : A' →* M)
    (hker : ∀ a : A', (a : G) ∈ N → f a = 1) (hAH : A' ≤ H ⊔ N) (hf : Function.Surjective f) :
    ∃ (B : Subgroup G) (g : B →* M), B ≤ H ∧ Function.Surjective g := by
  classical
  have hconj : ∀ a : A', ∀ n ∈ N, (a : G)⁻¹ * n * (a : G) ∈ N := by
    intro a n hn
    have := (Subgroup.mem_normalizer_iff.1 (hAN (A'.inv_mem a.2)) n).1 hn
    simpa using this
  let B : Subgroup G :=
    { carrier := {h | h ∈ H ∧ ∃ a : A', (a : G)⁻¹ * h ∈ N}
      mul_mem' := by
        rintro x y ⟨hx, a₁, ha₁⟩ ⟨hy, a₂, ha₂⟩
        refine ⟨H.mul_mem hx hy, a₁ * a₂, ?_⟩
        have h1 := N.mul_mem (hconj a₂ _ ha₁) ha₂
        have e : ((a₁ * a₂ : A') : G)⁻¹ * (x * y) =
            (a₂ : G)⁻¹ * ((a₁ : G)⁻¹ * x) * (a₂ : G) * ((a₂ : G)⁻¹ * y) := by
          simp only [Subgroup.coe_mul, mul_inv_rev]
          group
        rw [e]
        exact h1
      one_mem' := ⟨H.one_mem, 1, by simp⟩
      inv_mem' := by
        rintro h ⟨hh, a, ha⟩
        refine ⟨H.inv_mem hh, a⁻¹, ?_⟩
        have h2 := (Subgroup.mem_normalizer_iff.1 (hAN a.2) ((a : G)⁻¹ * h)⁻¹).1 (N.inv_mem ha)
        have e : (((a⁻¹ : A') : G))⁻¹ * h⁻¹ = (a : G) * ((a : G)⁻¹ * h)⁻¹ * (a : G)⁻¹ := by
          simp only [Subgroup.coe_inv, inv_inv]
          group
        rw [e]
        exact h2 }
  have hwd : ∀ (h : G) (a b : A'), (a : G)⁻¹ * h ∈ N → (b : G)⁻¹ * h ∈ N → f a = f b := by
    intro h a b ha hb
    have h1 : (a : G)⁻¹ * (b : G) ∈ N := by
      have := N.mul_mem ha (N.inv_mem hb)
      simpa [mul_assoc] using this
    have h2 : f (a⁻¹ * b) = 1 := hker (a⁻¹ * b) (by simpa using h1)
    rw [map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have hB : ∀ h : B, ∃ a : A', (a : G)⁻¹ * (h : G) ∈ N := fun h => h.2.2
  let g : B →* M :=
    { toFun := fun h => f (Classical.choose (hB h))
      map_one' := by
        have h1 := Classical.choose_spec (hB 1)
        have h0 : ((1 : A') : G)⁻¹ * ((1 : B) : G) ∈ N := by simp
        rw [hwd _ _ _ h1 h0, map_one]
      map_mul' := by
        intro h₁ h₂
        have h1 := Classical.choose_spec (hB h₁)
        have h2 := Classical.choose_spec (hB h₂)
        have h12 := Classical.choose_spec (hB (h₁ * h₂))
        have hprod : ((Classical.choose (hB h₁) * Classical.choose (hB h₂) : A') : G)⁻¹ *
            ((h₁ * h₂ : B) : G) ∈ N := by
          have h3 := N.mul_mem (hconj (Classical.choose (hB h₂)) _ h1) h2
          have : ((Classical.choose (hB h₁) * Classical.choose (hB h₂) : A') : G)⁻¹ *
              ((h₁ * h₂ : B) : G) = ((Classical.choose (hB h₂) : A') : G)⁻¹ *
              (((Classical.choose (hB h₁) : A') : G)⁻¹ * (h₁ : G)) *
              ((Classical.choose (hB h₂) : A') : G) *
              (((Classical.choose (hB h₂) : A') : G)⁻¹ * (h₂ : G)) := by
            simp only [Subgroup.coe_mul, mul_inv_rev]
            group
          rw [this]
          exact h3
        rw [hwd _ _ _ h12 hprod, map_mul] }
  refine ⟨B, g, fun h hh => hh.1, fun m => ?_⟩
  obtain ⟨a, rfl⟩ := hf m
  obtain ⟨h, hh, n, hn, hhn⟩ := mem_sup_of_le_normalizer hHN (hAH a.2)
  have hBh : h ∈ B := ⟨hh, a, by rw [hhn]; simp [N.inv_mem hn]⟩
  refine ⟨⟨h, hBh⟩, ?_⟩
  have h1 := Classical.choose_spec (hB ⟨h, hBh⟩)
  have h0 : (a : G)⁻¹ * h ∈ N := by rw [hhn]; simpa using N.inv_mem hn
  show f (Classical.choose (hB ⟨h, hBh⟩)) = f a
  exact hwd h _ _ h1 h0

theorem exists_quotient_section [IsSimpleGroup M] (hM : ¬ IsPGroup 2 M) {H : Type*} [Group H]
    (Z : Subgroup H) [Z.Normal] (hZ : IsPGroup 2 Z) (B : Subgroup H) (g : B →* M)
    (hg : Function.Surjective g) :
    ∃ (C : Subgroup (H ⧸ Z)) (g' : C →* M), Function.Surjective g' := by
  let π : H →* H ⧸ Z := QuotientGroup.mk' Z
  let ψ : B →* B.map π := π.subgroupMap B
  have hψ : Function.Surjective ψ := π.subgroupMap_surjective B
  have hker : ψ.ker ≤ g.ker := by
    intro b hb
    have hb1 : π b = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hb)
    have hbZ : (b : H) ∈ Z := (QuotientGroup.eq_one_iff _).1 hb1
    have hZB : IsPGroup 2 (Z.subgroupOf B) := hZ.comap_subtype
    have : Z.subgroupOf B ≤ g.ker := normal_pGroup_le_ker hM g hg hZB
    exact this hbZ
  refine ⟨B.map π, ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ)
    ⟨g, hker⟩, ?_⟩
  intro m
  obtain ⟨b, rfl⟩ := hg m
  exact ⟨ψ b, MonoidHom.liftOfRightInverse_comp_apply ψ _ _ _ b⟩

end Descent


section Sup

variable {M : Type*} [Group M] {G : Type*} [Group G]

theorem sec_of_sup [IsSimpleGroup M] (hM : ¬ IsPGroup 2 M) (L L' R : Subgroup G)
    (hRL : L ≤ Subgroup.normalizer (R : Set G)) (hRL' : L' ≤ Subgroup.normalizer (R : Set G))
    (hR : IsPGroup 2 R) (hcomm : ⁅L, L'⁆ ≤ R) (A : Subgroup G) (hA : A ≤ L ⊔ L') (f : A →* M)
    (hf : Function.Surjective f) :
    (∃ (B : Subgroup G) (g : B →* M), B ≤ L ∧ Function.Surjective g) ∨
      (∃ (B : Subgroup G) (g : B →* M), B ≤ L' ∧ Function.Surjective g) := by
  classical
  set P : Subgroup G := L ⊔ R with hP
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := fun l hl =>
    Subgroup.le_normalizer (Subgroup.mem_sup_left hl)
  have hL'P : L' ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ l ∈ L', ∀ x ∈ P, l * x * l⁻¹ ∈ P := by
      intro l hl x hx
      have hle : L ⊔ R ≤ P.comap (MulAut.conj l).toMonoidHom := by
        refine sup_le (fun y hy => ?_) (fun y hy => ?_)
        · have h1 : ⁅y⁻¹, l⁆ ∈ R :=
            hcomm (Subgroup.commutator_mem_commutator (L.inv_mem hy) hl)
          have e : (MulAut.conj l).toMonoidHom y = y * ⁅y⁻¹, l⁆ := by
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def, inv_inv]
            group
          show (MulAut.conj l).toMonoidHom y ∈ P
          rw [e]
          exact P.mul_mem (Subgroup.mem_sup_left hy) (Subgroup.mem_sup_right h1)
        · have h2 := (Subgroup.mem_normalizer_iff.1 (hRL' hl) y).1 hy
          show (MulAut.conj l).toMonoidHom y ∈ P
          exact Subgroup.mem_sup_right h2
      exact hle hx
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => key l hl x hx, fun hx => ?_⟩
    have h1 := key l⁻¹ (L'.inv_mem hl) _ hx
    have e : l⁻¹ * (l * x * l⁻¹) * l = x := by group
    rw [inv_inv] at h1
    simpa [e] using h1
  have hAnP : A ≤ Subgroup.normalizer (P : Set G) := fun a ha => sup_le hLP hL'P (hA ha)
  have hAnR : A ≤ Subgroup.normalizer (R : Set G) := hA.trans (sup_le hRL hRL')
  have hZn : (P.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAnP
  have hZmap : ((P.subgroupOf A).map f).Normal := Subgroup.Normal.map hZn f hf
  have hRn : (R.subgroupOf A).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hAnR
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((P.subgroupOf A).map f) with h | h
  ·
    right
    refine exists_hom_of_normalizes A L' P hAnP hL'P f ?_ (hA.trans (sup_le
      (le_trans le_sup_left le_sup_right) le_sup_left)) hf
    intro a ha
    have : f a ∈ (P.subgroupOf A).map f := ⟨a, ha, rfl⟩
    rw [h, Subgroup.mem_bot] at this
    exact this
  ·
    left
    let f' : (A ⊓ P : Subgroup G) →* M := f.comp (Subgroup.inclusion inf_le_left)
    have hf' : Function.Surjective f' := by
      intro m
      have hm : m ∈ (P.subgroupOf A).map f := by rw [h]; exact Subgroup.mem_top m
      obtain ⟨a, ha, rfl⟩ := hm
      exact ⟨⟨a.1, a.2, ha⟩, rfl⟩
    have hRker : R.subgroupOf A ≤ f.ker :=
      normal_pGroup_le_ker hM f hf (hR.comap_subtype)
    refine exists_hom_of_normalizes (A ⊓ P) L R (inf_le_left.trans hAnR) hRL f' ?_
      inf_le_right hf'
    intro a ha
    exact hRker (show (⟨a.1, a.2.1⟩ : A) ∈ R.subgroupOf A from ha)

end Sup

section Lift

variable {M : Type*} [Group M]

theorem exists_two_subgroup_map_eq {B : Type*} [Group B] [Finite B] (φ : B →* M)
    (hφ : Function.Surjective φ) (E : Subgroup M) (hE : IsPGroup 2 E) :
    ∃ S : Subgroup B, IsPGroup 2 S ∧ S.map φ = E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup B := E.comap φ
  let ψ : C →* E := (φ.comp C.subtype).codRestrict E (fun c => c.2)
  have hψ : Function.Surjective ψ := by
    intro e
    obtain ⟨b, hb⟩ := hφ (e : M)
    exact ⟨⟨b, by show φ b ∈ E; rw [hb]; exact e.2⟩, Subtype.ext hb⟩
  obtain ⟨T⟩ : Nonempty (Sylow 2 C) := inferInstance
  have htop : IsPGroup 2 (⊤ : Subgroup ↥E) := fun x => by
    obtain ⟨k, hk⟩ := hE x.1
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun y : ↥E => (y : M)) hk))⟩
  have hT' : ((Sylow.mapSurjective hψ T : Sylow 2 E) : Subgroup E) = ⊤ :=
    ((Sylow.mapSurjective hψ T : Sylow 2 E).is_maximal' htop le_top).symm
  refine ⟨(T : Subgroup C).map C.subtype, T.isPGroup'.map _, ?_⟩
  have hcomp : φ.comp C.subtype = E.subtype.comp ψ := by
    ext c
    rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  have hmap : (T : Subgroup C).map ψ = ⊤ := by
    have := Sylow.coe_mapSurjective hψ T
    rw [hT'] at this
    exact this.symm
  rw [hmap, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end Lift

section CyclicIndexTwo

def HasCyclicIndexTwo (Γ : Type*) [Group Γ] : Prop :=
  ∃ N : Subgroup Γ, N.Normal ∧ IsCyclic N ∧ N.index ∣ 2

theorem HasCyclicIndexTwo.of_surjective {Γ Δ : Type*} [Group Γ] [Group Δ] (φ : Γ →* Δ)
    (hφ : Function.Surjective φ) (h : HasCyclicIndexTwo Γ) : HasCyclicIndexTwo Δ := by
  obtain ⟨N, hN, hcyc, hidx⟩ := h
  refine ⟨N.map φ, Subgroup.Normal.map hN φ hφ, ?_, ?_⟩
  · exact isCyclic_of_surjective (φ.subgroupMap N) (φ.subgroupMap_surjective N)
  · exact (Subgroup.index_map_dvd N hφ).trans hidx

theorem HasCyclicIndexTwo.of_injective {Θ Γ : Type*} [Group Θ] [Group Γ] (ι : Θ →* Γ)
    (hι : Function.Injective ι) (h : HasCyclicIndexTwo Γ) : HasCyclicIndexTwo Θ := by
  obtain ⟨N, hN, hcyc, hidx⟩ := h
  refine ⟨N.comap ι, Subgroup.Normal.comap hN ι, ?_, ?_⟩
  · refine isCyclic_of_injective (G' := N)
      ((ι.comp (N.comap ι).subtype).codRestrict N fun x => x.2) ?_
    intro x y hxy
    exact Subtype.ext (hι (congrArg Subtype.val hxy))
  · rw [Subgroup.index_comap]
    exact (Subgroup.relIndex_dvd_index_of_normal N ι.range).trans hidx

theorem hasCyclicIndexTwo_dihedral {n : ℕ} (hn : n ≠ 0) : HasCyclicIndexTwo (DihedralGroup n) := by
  have h1 : Nat.card (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)) = n := by
    rw [Nat.card_zpowers, DihedralGroup.orderOf_r_one]
  have h2 := Subgroup.card_mul_index (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n))
  rw [h1, DihedralGroup.nat_card] at h2
  have h3 : (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)).index = 2 := by
    have : n * (Subgroup.zpowers (DihedralGroup.r 1 : DihedralGroup n)).index = n * 2 := by
      rw [h2]; ring
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hn) this
  have := Subgroup.normal_of_index_eq_two h3
  exact ⟨_, this, inferInstance, h3.symm ▸ dvd_rfl⟩

theorem card_le_four_of_exponent_two {Γ : Type*} [Group Γ] (h : HasCyclicIndexTwo Γ) (E : Subgroup Γ)
    (hE : ∀ x ∈ E, x ^ 2 = 1) : Nat.card E ≤ 4 := by
  obtain ⟨N, hN, hcyc, hidx⟩ := h
  have hcyc' : IsCyclic (N.subgroupOf E) := by
    refine isCyclic_of_injective (G' := N)
      ((E.subtype.comp (N.subgroupOf E).subtype).codRestrict N fun x => x.2) ?_
    intro x y hxy
    have h1 : ((x : E) : Γ) = ((y : E) : Γ) := congrArg (fun z : ↥N => (z : Γ)) hxy
    exact Subtype.ext (Subtype.ext h1)
  have hexp : Monoid.exponent (N.subgroupOf E) ∣ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
    exact Subtype.ext (Subtype.ext (hE x.1.1 x.1.2))
  have hc1 : Nat.card (N.subgroupOf E) ≤ 2 := by
    have := IsCyclic.exponent_eq_card (α := N.subgroupOf E)
    rw [this] at hexp
    exact Nat.le_of_dvd (by norm_num) hexp
  have h2 := Subgroup.card_mul_index (N.subgroupOf E)
  have h3 : (N.subgroupOf E).index ≤ 2 :=
    Nat.le_of_dvd (by norm_num) ((Subgroup.relIndex_dvd_index_of_normal N E).trans hidx)
  rw [← h2]
  calc Nat.card (N.subgroupOf E) * (N.subgroupOf E).index ≤ 2 * 2 := Nat.mul_le_mul hc1 h3
    _ = 4 := by norm_num

end CyclicIndexTwo


section Generated

variable {Γ : Type*} [Group Γ]

theorem pow_two_eq_one_of_closure (S : Set Γ) (hS2 : ∀ x ∈ S, x ^ 2 = 1)
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) : ∀ x ∈ Subgroup.closure S, x ^ 2 = 1 := by
  have h1 : Subgroup.closure S ≤ Subgroup.centralizer S := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_iff.2 fun h hh => hcomm h hh x hx
  have h2 : Subgroup.closure S ≤ Subgroup.centralizer (Subgroup.centralizer S : Set Γ) :=
    Subgroup.closure_le_centralizer_centralizer S
  have hc : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.1 (h2 hy) x (h1 hx)
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hS2 x hx
  | one => simp
  | mul x y hx hy ihx ihy =>
    calc (x * y) ^ 2 = x * y * (x * y) := sq _
      _ = x * x * (y * y) := by rw [mul_assoc, ← mul_assoc y x y, ← hc x hx y hy, mul_assoc, mul_assoc]
      _ = x ^ 2 * y ^ 2 := by rw [sq, sq]
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx =>
    rw [inv_pow, ihx, inv_one]

theorem pow_four_eq_one_of_dihedral (u v : Γ) (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (huv : (u * v) ^ 4 = 1) :
    ∀ x ∈ Subgroup.closure {u, v}, x ^ 4 = 1 := by
  have huu : u * u = 1 := by rw [← sq]; exact hu
  have hvv : v * v = 1 := by rw [← sq]; exact hv
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right huu
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hvv
  have hconj : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, hu', hv']
    calc u * (u * v) * u = (u * u) * v * u := by group
      _ = v * u := by rw [huu, one_mul]
  have hconjz : ∀ k : ℤ, u * (u * v) ^ k = (u * v) ^ (-k) * u := by
    intro k
    have h1 : u * (u * v) ^ k * u⁻¹ = (u * v) ^ (-k) := by
      rw [← conj_zpow, hconj, inv_zpow, zpow_neg]
    exact (mul_inv_eq_iff_eq_mul.1 h1)
  let D : Subgroup Γ :=
    { carrier := {x | ∃ k : ℤ, x = (u * v) ^ k ∨ x = (u * v) ^ k * u}
      mul_mem' := by
        rintro x y ⟨a, ha | ha⟩ ⟨b, hb | hb⟩ <;> subst ha <;> subst hb
        · exact ⟨a + b, Or.inl (by rw [zpow_add])⟩
        · exact ⟨a + b, Or.inr (by rw [zpow_add, mul_assoc])⟩
        · refine ⟨a - b, Or.inr ?_⟩
          calc (u * v) ^ a * u * (u * v) ^ b = (u * v) ^ a * (u * (u * v) ^ b) := mul_assoc _ _ _
            _ = (u * v) ^ a * ((u * v) ^ (-b) * u) := by rw [hconjz b]
            _ = ((u * v) ^ a * (u * v) ^ (-b)) * u := (mul_assoc _ _ _).symm
            _ = (u * v) ^ (a - b) * u := by rw [← zpow_add, ← sub_eq_add_neg]
        · refine ⟨a - b, Or.inl ?_⟩
          calc (u * v) ^ a * u * ((u * v) ^ b * u)
              = (u * v) ^ a * (u * (u * v) ^ b) * u := by simp only [mul_assoc]
            _ = (u * v) ^ a * ((u * v) ^ (-b) * u) * u := by rw [hconjz b]
            _ = ((u * v) ^ a * (u * v) ^ (-b)) * (u * u) := by simp only [mul_assoc]
            _ = (u * v) ^ (a - b) := by rw [← zpow_add, ← sub_eq_add_neg, huu, mul_one]
      one_mem' := ⟨0, Or.inl (by simp)⟩
      inv_mem' := by
        rintro x ⟨a, ha | ha⟩ <;> subst ha
        · exact ⟨-a, Or.inl (by rw [zpow_neg])⟩
        · refine ⟨a, Or.inr ?_⟩
          calc ((u * v) ^ a * u)⁻¹ = u⁻¹ * ((u * v) ^ a)⁻¹ := mul_inv_rev _ _
            _ = u * (u * v) ^ (-a) := by rw [hu', ← zpow_neg]
            _ = (u * v) ^ (- -a) * u := hconjz (-a)
            _ = (u * v) ^ a * u := by rw [neg_neg] }
  have hD : Subgroup.closure {u, v} ≤ D := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ⟨0, Or.inr (by simp)⟩
    · refine ⟨-1, Or.inr ?_⟩
      rw [zpow_neg, zpow_one, mul_inv_rev, hu', hv']
      calc x = x * (u * u) := by rw [huu, mul_one]
        _ = x * u * u := (mul_assoc _ _ _).symm
  intro x hx
  obtain ⟨k, hk | hk⟩ := hD hx
  · rw [hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    simp [huv]
  · have h2 : x ^ 2 = 1 := by
      rw [hk, sq]
      calc (u * v) ^ k * u * ((u * v) ^ k * u)
          = (u * v) ^ k * (u * (u * v) ^ k) * u := by simp only [mul_assoc]
        _ = (u * v) ^ k * ((u * v) ^ (-k) * u) * u := by rw [hconjz k]
        _ = ((u * v) ^ k * (u * v) ^ (-k)) * (u * u) := by simp only [mul_assoc]
        _ = 1 := by rw [← zpow_add, add_neg_cancel, zpow_zero, huu, mul_one]
    calc x ^ 4 = (x ^ 2) ^ 2 := by rw [← pow_mul]
      _ = 1 := by rw [h2, one_pow]

end Generated


section Misc

variable {G : Type*} [Group G]

theorem le_normalizer_commutator_left (A B : Subgroup G) :
    A ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have key : ∀ a ∈ A, ∀ c ∈ ⁅A, B⁆, a * c * a⁻¹ ∈ ⁅A, B⁆ := by
    intro a ha c hc
    have hle : ⁅A, B⁆ ≤ (⁅A, B⁆).comap (MulAut.conj a).toMonoidHom := by
      rw [Subgroup.commutator_def, Subgroup.closure_le]
      rintro _ ⟨x, hx, y, hy, rfl⟩
      show (MulAut.conj a).toMonoidHom ⁅x, y⁆ ∈ ⁅A, B⁆
      have e : (MulAut.conj a).toMonoidHom ⁅x, y⁆ = ⁅a * x, y⁆ * ⁅a, y⁆⁻¹ := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
        group
      rw [e]
      exact (⁅A, B⁆).mul_mem (Subgroup.commutator_mem_commutator (A.mul_mem ha hx) hy)
        ((⁅A, B⁆).inv_mem (Subgroup.commutator_mem_commutator ha hy))
    exact hle hc
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key a ha c hc, fun hc => ?_⟩
  have h1 := key a⁻¹ (A.inv_mem ha) _ hc
  have e : a⁻¹ * (a * c * a⁻¹) * a⁻¹⁻¹ = c := by group
  rwa [e] at h1

theorem le_normalizer_commutator_right (A B : Subgroup G) :
    B ≤ Subgroup.normalizer ((⁅A, B⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.commutator_comm]
  exact le_normalizer_commutator_left B A

theorem exists_section_of_le_map {M : Type*} [Group M] (e : G ≃* G) {X B : Subgroup G}
    (hB : B ≤ X.map e.toMonoidHom) (g : B →* M) (hg : Function.Surjective g) :
    ∃ (B' : Subgroup G) (g' : B' →* M), B' ≤ X ∧ Function.Surjective g' := by
  refine ⟨B.map e.symm.toMonoidHom, g.comp (e.symm.subgroupMap B).symm.toMonoidHom, ?_, ?_⟩
  · rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hx, hxb⟩ := hB hb
    have : e.symm b = x := by rw [← hxb]; simp
    show e.symm b ∈ X
    rw [this]
    exact hx
  · exact hg.comp (e.symm.subgroupMap B).symm.surjective

theorem exists_section_subgroupOf {M : Type*} [Group M] {L B : Subgroup G} (hB : B ≤ L) (g : B →* M)
    (hg : Function.Surjective g) :
    ∃ (C : Subgroup ↥L) (g' : C →* M), Function.Surjective g' :=
  ⟨B.subgroupOf L, g.comp (Subgroup.subgroupOfEquivOfLe hB).toMonoidHom,
    hg.comp (Subgroup.subgroupOfEquivOfLe hB).surjective⟩

theorem exists_section_of_mulEquiv {X X' M : Type*} [Group X] [Group X'] [Group M] (e : X ≃* X')
    (C : Subgroup X) (g : C →* M) (hg : Function.Surjective g) :
    ∃ (C' : Subgroup X') (g' : C' →* M), Function.Surjective g' :=
  ⟨C.map e.toMonoidHom, g.comp (e.subgroupMap C).symm.toMonoidHom,
    hg.comp (e.subgroupMap C).symm.surjective⟩

end Misc

end CFSG.Quasithin.S152V
