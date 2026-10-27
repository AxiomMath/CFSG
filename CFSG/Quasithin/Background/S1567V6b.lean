module

public import CFSG.Quasithin.Background.S1567V5
public import CFSG.Quasithin.Background.S1567V6a

public section

namespace CFSG.Quasithin

open CFSG.Open
open scoped Matrix

namespace S1567

section Count

theorem card_map_mul_card_inf_ker {X Y : Type*} [Group X] [Group Y] (f : X →* Y) (S : Subgroup X) :
    Nat.card (S.map f) * Nat.card ↥(f.ker ⊓ S) = Nat.card S := by
  have h := Subgroup.relIndex_mul_card f.ker S
  rwa [Subgroup.relIndex_ker] at h

theorem add_self_eq_zero_of_card_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) (a : F) :
    a + a = 0 := by
  have h1 : ∀ b : ZMod 2, b + b = 0 := by decide
  exact (toZMod2 hF).injective (by simpa using h1 (toZMod2 hF a))

theorem mul_self_eq_one_of_card_two {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) {k : ℕ}
    {ι : Type} (y : Multiplicative (Fin k → ι → F)) : y * y = 1 := by
  apply Multiplicative.toAdd.injective
  funext i j
  simpa using add_self_eq_zero_of_card_two hF (Multiplicative.toAdd y i j)

structure Case3Mod {G : Type} [Group G] (L Q : Subgroup G) {F : Type} [Field F] [Fintype F]
    (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) : Prop where
  card_F : Fintype.card F = 2
  surj : Function.Surjective α
  nat : IsSumOfNaturalModulesVia L (centerOf Q) ⊥ α false 1
  dual : IsSumOfNaturalModulesVia L Q (centerOf Q) α true 2

end Count


section Irred

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

omit [Finite G] in
theorem card_case3 {L Q : Subgroup G} {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    (hm : Case3Mod L Q α) : Nat.card ↥(centerOf Q) = 8 ∧ Nat.card ↥Q = 512 := by
  have hF := hm.card_F
  have hZ : Nat.card ↥(centerOf Q) = 8 := by
    have h := card_of_isSumOfNaturalModulesVia hm.nat
    rw [Subgroup.card_bot, hF] at h
    simpa using h
  refine ⟨hZ, ?_⟩
  have h := card_of_isSumOfNaturalModulesVia hm.dual
  rw [hZ, hF] at h
  simpa using h

theorem centerOf_le_of_case3 {L Q V₀ : Subgroup G}
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hm : Case3Mod L Q α) (hV₀Q : V₀ ≤ Q)
    (hV₀L : L ≤ Subgroup.normalizer (V₀ : Set G)) (hV₀ab : IsElemAbelian 2 V₀)
    (hV₀64 : 64 ≤ Nat.card V₀) : centerOf Q ≤ V₀ := by
  classical
  have hF := hm.card_F
  obtain ⟨hZ, hQ⟩ := card_case3 hm
  obtain ⟨hLZ, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := hm.nat
  have hβ₁i : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₁k, Subgroup.bot_subgroupOf]
  have hZQ : centerOf Q ≤ Q := inf_le_left
  have hZc : ∀ z ∈ centerOf Q, ∀ q ∈ Q, z * q = q * z := fun z hz q hq =>
    (Subgroup.mem_centralizer_iff.mp hz.2 q hq).symm
  have hZab : IsElemAbelian 2 (centerOf Q) := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hZc x x.2 y (hZQ y.2))⟩⟩, fun x hx => ?_⟩
    have h1 : (⟨x, hx⟩ : ↥(centerOf Q)) ^ 2 = 1 := by
      apply hβ₁i
      rw [map_pow, pow_two, mul_self_eq_one_of_card_two hF, map_one]
    exact congrArg Subtype.val h1
  have hY : V₀ ⊓ centerOf Q ≠ ⊥ := by
    intro hY
    have hcomm : ∀ a ∈ V₀, ∀ b ∈ centerOf Q, a * b = b * a := fun a ha b hb =>
      (hZc b hb a (hV₀Q ha)).symm
    have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
    rw [hY, Subgroup.card_bot, mul_one, hZ] at hcard
    have hsupQ : V₀ ⊔ centerOf Q ≤ Q := sup_le hV₀Q hZQ
    have heq : V₀ ⊔ centerOf Q = Q :=
      Subgroup.eq_of_le_of_card_ge hsupQ (by rw [hcard, hQ]; omega)
    have hEA := B2F.isElemAbelian_sup_of_commute hV₀ab hZab hcomm
    rw [heq] at hEA
    have hle : Q ≤ centerOf Q := fun x hx =>
      ⟨hx, Subgroup.mem_centralizer_iff.mpr fun y hy => B2F.isElemAbelian_comm hEA hy hx⟩
    have := Subgroup.card_le_of_le hle
    omega
  obtain ⟨z, hzY, hz1⟩ : ∃ z ∈ V₀ ⊓ centerOf Q, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hY (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  intro z' hz'
  by_cases hz'1 : z' = 1
  · rw [hz'1]
    exact V₀.one_mem
  have hvec_ne : ∀ x : ↥(centerOf Q), x ≠ 1 → Multiplicative.toAdd (β₁ x) 0 ≠ 0 := by
    intro x hx h0
    apply hx
    apply hβ₁i
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simpa using h0
  obtain ⟨g, -, hgv⟩ := exists_inv_mulVec hF false (Multiplicative.toAdd (β₁ ⟨z, hzY.2⟩) 0)
    (Multiplicative.toAdd (β₁ ⟨z', hz'⟩) 0) (hvec_ne _ fun h => hz1 (congrArg Subtype.val h))
    (hvec_ne _ fun h => hz'1 (congrArg Subtype.val h))
  obtain ⟨l, hl⟩ := hm.surj ⟨g, mem_statedSL_of_card_two hF g⟩
  have hlz : (l : G) * z * (l : G)⁻¹ ∈ centerOf Q :=
    (Subgroup.mem_normalizer_iff.mp (hLZ l.2) z).mp hzY.2
  have hlzV : (l : G) * z * (l : G)⁻¹ ∈ V₀ :=
    (Subgroup.mem_normalizer_iff.mp (hV₀L l.2) z).mp hzY.1
  have hconj : (⟨(l : G) * z * (l : G)⁻¹, hlz⟩ : ↥(centerOf Q)) = ⟨z', hz'⟩ := by
    apply hβ₁i
    apply Multiplicative.toAdd.injective
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h := hβ₁e l ⟨z, hzY.2⟩ ⟨(l : G) * z * (l : G)⁻¹, hlz⟩ rfl 0
    rw [h, hl]
    exact hgv
  have : z' = (l : G) * z * (l : G)⁻¹ := (congrArg Subtype.val hconj).symm
  rw [this]
  exact hlzV

end Irred

section Index

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

omit [Finite G] [Fintype F] in
@[expose] def imGL (L D : Subgroup G) (α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
    Subgroup (Matrix.GeneralLinearGroup (Fin 3) F) :=
  (D.subgroupOf L).map ((CFSG.Assembly.LowTwoRank.StatedSL 3 F).subtype.comp α)

omit [Finite G] [Fintype F] in
theorem mem_imGL {L D : Subgroup G} {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)}
    {b : Matrix.GeneralLinearGroup (Fin 3) F} :
    b ∈ imGL L D α ↔ ∃ a : ↥L, (a : G) ∈ D ∧ ((α a : ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)) :
      Matrix.GeneralLinearGroup (Fin 3) F) = b := by
  unfold imGL
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_comp, Subgroup.coe_subtype,
    Function.comp_apply]

theorem card_le_ncard_of_toAdd {P : Subgroup (Multiplicative (Fin 3 → F))} {S : Set (Fin 3 → F)}
    (h : ∀ y ∈ P, Multiplicative.toAdd y ∈ S) : Nat.card P ≤ Set.ncard S := by
  calc Nat.card P = Set.ncard (P : Set (Multiplicative (Fin 3 → F))) := (Nat.card_coe_set_eq _).symm
    _ = Set.ncard (Multiplicative.toAdd '' (P : Set (Multiplicative (Fin 3 → F)))) :=
        (Set.ncard_image_of_injective _ Multiplicative.toAdd.injective).symm
    _ ≤ Set.ncard S := Set.ncard_le_ncard (by rintro _ ⟨y, hy, rfl⟩; exact h y hy) (Set.toFinite _)

omit [Field F] in
theorem natCard_multiplicative_fin_three (hF : Fintype.card F = 2) :
    Nat.card (Multiplicative (Fin 3 → F)) = 8 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_eq_fintype_card, Fintype.card_fun, hF]
  simp

end Index

theorem arith_aux (m n v p k c cs : ℕ) (hv : v = k * 8) (hk : p * 8 = k) (hCle : m ≤ cs * (p * c))
    (hfix : c * cs * n ≤ 32) (hpos : 0 < p) : n * m < v := by
  have h1 : n * m ≤ n * (cs * (p * c)) := Nat.mul_le_mul_left _ hCle
  have h2 : n * (cs * (p * c)) = p * (c * cs * n) := by ring
  have h3 : p * (c * cs * n) ≤ p * 32 := Nat.mul_le_mul_left _ hfix
  omega

section MainIndex

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

theorem index_gt_of_case3 {L Q V₀ D : Subgroup G}
    {α : ↥L →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)} (hm : Case3Mod L Q α) (hV₀Q : V₀ ≤ Q)
    (hV₀L : L ≤ Subgroup.normalizer (V₀ : Set G)) (hV₀ab : IsElemAbelian 2 V₀)
    (hV₀64 : 64 ≤ Nat.card V₀)
    (hΛab : IsElemAbelian 2 (imGL L D α)) (hΛ1 : imGL L D α ≠ ⊥) :
    Nat.card (imGL L D α) * Nat.card ↥(V₀ ⊓ Subgroup.centralizer (D : Set G)) < Nat.card V₀ := by
  classical
  have hF := hm.card_F
  have hZV : centerOf Q ≤ V₀ := centerOf_le_of_case3 hm hV₀Q hV₀L hV₀ab hV₀64
  obtain ⟨hZ, hQ⟩ := card_case3 hm
  obtain ⟨hLZ, -, β₁, hβ₁s, hβ₁k, hβ₁e⟩ := hm.nat
  obtain ⟨hLQ, -, β₂, hβ₂s, hβ₂k, hβ₂e⟩ := hm.dual
  have hβ₁i : Function.Injective β₁ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβ₁k, Subgroup.bot_subgroupOf]
  have hZQ : centerOf Q ≤ Q := inf_le_left
  set C := V₀ ⊓ Subgroup.centralizer (D : Set G) with hC
  have hCV : C ≤ V₀ := inf_le_left
  let ι : ↥V₀ →* ↥Q := Subgroup.inclusion hV₀Q
  let ψ : ↥V₀ →* Multiplicative (Fin 2 → Fin 3 → F) := β₂.comp ι
  have hψk : ψ.ker = (centerOf Q).subgroupOf V₀ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have : β₂ (ι x) = 1 ↔ ι x ∈ β₂.ker := (MonoidHom.mem_ker).symm
    show β₂ (ι x) = 1 ↔ (x : G) ∈ centerOf Q
    rw [this, hβ₂k, Subgroup.mem_subgroupOf]
    rfl
  obtain ⟨v, hvV, hvZ⟩ : ∃ v ∈ V₀, v ∉ centerOf Q := by
    by_contra hcon
    push Not at hcon
    have h1 := Subgroup.card_le_of_le (fun x hx => hcon x hx : V₀ ≤ centerOf Q)
    omega
  obtain ⟨i, hvi⟩ : ∃ i : Fin 2, Multiplicative.toAdd (ψ ⟨v, hvV⟩) i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hvZ
    have h1 : ψ ⟨v, hvV⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext j
      simpa using hcon j
    have h2 : (⟨v, hvV⟩ : ↥V₀) ∈ ψ.ker := h1
    rw [hψk, Subgroup.mem_subgroupOf] at h2
    exact h2
  let π : Multiplicative (Fin 2 → Fin 3 → F) →* Multiplicative (Fin 3 → F) :=
    AddMonoidHom.toMultiplicative (Pi.evalAddMonoidHom (fun _ : Fin 2 => Fin 3 → F) i)
  let θ : ↥V₀ →* Multiplicative (Fin 3 → F) := π.comp ψ
  have hθ_apply : ∀ x : ↥V₀, Multiplicative.toAdd (θ x) = Multiplicative.toAdd (ψ x) i := fun x => rfl
  have hθs : Function.Surjective θ := by
    intro w
    by_cases hw : w = 1
    · exact ⟨1, by rw [hw, map_one]⟩
    have hw0 : Multiplicative.toAdd w ≠ 0 := fun h => hw (Multiplicative.toAdd.injective (by simpa using h))
    obtain ⟨g, -, hgv⟩ := exists_inv_mulVec hF true (Multiplicative.toAdd (ψ ⟨v, hvV⟩) i)
      (Multiplicative.toAdd w) hvi hw0
    obtain ⟨l, hl⟩ := hm.surj ⟨g, mem_statedSL_of_card_two hF g⟩
    have hlvV : (l : G) * v * (l : G)⁻¹ ∈ V₀ := (Subgroup.mem_normalizer_iff.mp (hV₀L l.2) v).mp hvV
    refine ⟨⟨(l : G) * v * (l : G)⁻¹, hlvV⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    have h := hβ₂e l ⟨v, hV₀Q hvV⟩ ⟨(l : G) * v * (l : G)⁻¹, hV₀Q hlvV⟩ rfl i
    rw [hθ_apply]
    show Multiplicative.toAdd (β₂ ⟨_, _⟩) i = _
    rw [h, hl]
    exact hgv
  have hθk : ψ.ker ≤ θ.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    show π (ψ x) = 1
    rw [hx, map_one]
  have hi := Subgroup.card_ker_mul_card_of_surjective hθs
  rw [natCard_multiplicative_fin_three hF] at hi
  have hψk8 : Nat.card ψ.ker = 8 := by
    rw [hψk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZV).toEquiv, hZ]
  have hiv := card_map_mul_card_inf_ker ψ θ.ker
  rw [inf_eq_left.mpr hθk, hψk8] at hiv
  set Cx := C.subgroupOf V₀ with hCx
  have hCxC : Nat.card Cx = Nat.card C := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCV).toEquiv
  have hii := card_map_mul_card_inf_ker θ Cx
  set S₁ := θ.ker ⊓ Cx with hS₁
  have hiii := card_map_mul_card_inf_ker ψ S₁
  have hcommD : ∀ x ∈ C, ∀ a : ↥L, (a : G) ∈ D → (x : G) = (a : G) * x * (a : G)⁻¹ := by
    intro x hx a haD
    have h := Subgroup.mem_centralizer_iff.mp hx.2 (a : G) haD
    rw [h]
    group
  have ha : Nat.card (Cx.map θ) ≤
      Set.ncard {x : Fin 3 → F | ∀ b ∈ imGL L D α, (moduleAct true b).mulVec x = x} := by
    refine card_le_ncard_of_toAdd fun y hy => ?_
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
    intro b hb
    obtain ⟨a, haD, rfl⟩ := mem_imGL.mp hb
    have hxC : ((x : ↥V₀) : G) ∈ C := Subgroup.mem_subgroupOf.mp hx
    have h := hβ₂e a ⟨x, hV₀Q x.2⟩ ⟨x, hV₀Q x.2⟩ (hcommD _ hxC a haD) i
    exact h.symm
  have hyz0 : ∀ x : ↥V₀, x ∈ ψ.ker → (x : G) ∈ centerOf Q := fun x hx => by
    rw [hψk, Subgroup.mem_subgroupOf] at hx
    exact hx
  have hyz : ∀ y : ↥(ψ.ker ⊓ S₁), ((y : ↥V₀) : G) ∈ centerOf Q := fun y =>
    hyz0 _ (Subgroup.mem_inf.mp y.2).1
  have hyC : ∀ y : ↥(ψ.ker ⊓ S₁), ((y : ↥V₀) : G) ∈ C := fun y =>
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp y.2).2).2
  have hb : Nat.card ↥(ψ.ker ⊓ S₁) ≤
      Set.ncard {x : Fin 3 → F | ∀ b ∈ imGL L D α, (moduleAct false b).mulVec x = x} := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_le_card_of_injective
      (fun y => ⟨Multiplicative.toAdd (β₁ ⟨((y : ↥V₀) : G), hyz y⟩) 0, fun b hb => ?_⟩) ?_
    · obtain ⟨a, haD, rfl⟩ := mem_imGL.mp hb
      have h := hβ₁e a ⟨((y : ↥V₀) : G), hyz y⟩ ⟨((y : ↥V₀) : G), hyz y⟩
        (hcommD _ (hyC y) a haD) 0
      exact h.symm
    · intro y y' hyy
      have h1 : Multiplicative.toAdd (β₁ ⟨((y : ↥V₀) : G), hyz y⟩) 0 =
          Multiplicative.toAdd (β₁ ⟨((y' : ↥V₀) : G), hyz y'⟩) 0 := congrArg Subtype.val hyy
      have h2 : β₁ ⟨((y : ↥V₀) : G), hyz y⟩ = β₁ ⟨((y' : ↥V₀) : G), hyz y'⟩ := by
        apply Multiplicative.toAdd.injective
        funext j
        have hj : j = 0 := Subsingleton.elim _ _
        subst hj
        exact h1
      have h3 := hβ₁i h2
      have h4 : ((y : ↥V₀) : G) = ((y' : ↥V₀) : G) :=
        congrArg (fun z : ↥(centerOf Q) => (z : G)) h3
      exact Subtype.ext (Subtype.ext h4)
  have hc : Nat.card (S₁.map ψ) ≤ Nat.card (θ.ker.map ψ) :=
    Subgroup.card_le_of_le (Subgroup.map_mono (inf_le_left : S₁ ≤ θ.ker))
  have hfix := fix_card_mul_le hF (imGL L D α) hΛab hΛ1
  have hpos : 0 < Nat.card (θ.ker.map ψ) := Nat.card_pos
  have hCle : Nat.card C ≤ Set.ncard {x : Fin 3 → F | ∀ b ∈ imGL L D α, (moduleAct true b).mulVec x = x} *
      (Nat.card (θ.ker.map ψ) *
        Set.ncard {x : Fin 3 → F | ∀ b ∈ imGL L D α, (moduleAct false b).mulVec x = x}) := by
    rw [← hCxC, ← hii, ← hiii]
    exact Nat.mul_le_mul ha (Nat.mul_le_mul hc hb)
  exact arith_aux _ _ _ _ _ _ _ hi.symm hiv hCle hfix hpos

end MainIndex

end S1567

end CFSG.Quasithin
