module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4310Mod
public import CFSG.Quasithin.Vol2.Ch4Sec3C136Grp
public import CFSG.Quasithin.Vol2.Ch4Sec3C136Uni
public import CFSG.Quasithin.Vol2.Ch4Sec3C136One

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map {G' : Type} [Group G'] {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (f : G →* G') : IsElemAbelian 2 (B.map f) := CFSG.SectionRank.isElemAbelian_map hB _

theorem exists_isMaxElemAbelian_ne {G₀ R₀ Q S : Subgroup G} (hMS : IsMSPair G₀ R₀)
    (hS : IsSylowTwoOf S G₀) (hQO : Q ≤ pCoreOf 2 G₀)
    (hGQ : G₀ ≤ Subgroup.normalizer (Q : Set G)) (hQ1 : Q ≠ ⊥) (hQel : IsElemAbelian 2 Q)
    (hmax : ∀ B : Subgroup G, B ≤ G₀ → IsElemAbelian 2 B → Nat.card B ≤ Nat.card Q) :
    ∃ A : Subgroup G, IsMaxElemAbelian S A ∧ A ≠ Q := by
  by_contra hcon
  push Not at hcon
  have hR : R₀ ≤ G₀ ∧ pCoreOf 2 G₀ ≤ R₀ := by
    rcases hMS.2.1 with ⟨H', hH'lt, hodd, rfl⟩ | ⟨hRG, hOR, -⟩
    · refine ⟨(pCoreOf_le 2 H').trans hH'lt.le, ?_⟩
      obtain ⟨P, hP⟩ := exists_isSylowTwoOf H'
      have hPG : IsSylowTwoOf P G₀ := by
        refine ⟨hP.1.trans hH'lt.le, hP.2.1, fun h2 => ?_⟩
        have h1 := Subgroup.relIndex_mul_relIndex P H' G₀ hP.1 hH'lt.le
        have h3 : 2 ∣ P.relIndex H' * H'.relIndex G₀ := h1 ▸ h2
        rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h3 with h | h
        · exact hP.2.2 h
        · exact hodd h
      exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_two_le_of_isSylowTwoOf hPG).trans hP.1)
        (hH'lt.le.trans (le_normalizer_pCoreOf 2 G₀)) (pCoreOf_isPGroup 2 G₀)
    · exact ⟨hRG, hOR⟩
  obtain ⟨hRG, hOR⟩ := hR
  have hQR : Q ≤ R₀ := hQO.trans hOR
  refine hMS.2.2 Q hQR hQ1 ?_ hGQ
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  set B := ((Q.subgroupOf R₀).map φ.toMonoidHom).map R₀.subtype with hBdef
  have hBR : B ≤ R₀ := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hQsub : IsElemAbelian 2 (Q.subgroupOf R₀) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => Subtype.ext ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      show (((x : ↥(Q.subgroupOf R₀)) : ↥R₀) : G) * (((y : ↥(Q.subgroupOf R₀)) : ↥R₀) : G) =
        (((y : ↥(Q.subgroupOf R₀)) : ↥R₀) : G) * (((x : ↥(Q.subgroupOf R₀)) : ↥R₀) : G)
      exact congrArg Subtype.val (hQel.1.is_comm.comm ⟨_, x.2⟩ ⟨_, y.2⟩)
    · exact hQel.2 _ hx
  have hBel : IsElemAbelian 2 B := isElemAbelian_map (isElemAbelian_map hQsub _) _
  have hBcard : Nat.card B = Nat.card Q := by
    rw [hBdef, Subgroup.card_map_of_injective R₀.subtype_injective,
      Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv]
  have hB2 : IsPGroup 2 B := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hBel.2 _ x.2]; rfl)⟩
  obtain ⟨S', hBS', hS'⟩ := exists_isSylowTwoOf_of_le (hBR.trans hRG) hB2
  obtain ⟨h, hhG, hS'eq⟩ := hS.exists_conj hS'
  set B₀ := B.map (MulAut.conj h⁻¹).toMonoidHom with hB₀
  have hB₀S : B₀ ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hBS' hx
    rw [hS'eq] at hx'
    obtain ⟨s, hs, rfl⟩ := hx'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show h⁻¹ * (h * s * h⁻¹) * h⁻¹⁻¹ = s by group]
    exact hs
  have hB₀card : Nat.card B₀ = Nat.card Q := by
    rw [hB₀, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hBcard]
  have hB₀max : IsMaxElemAbelian S B₀ := by
    refine ⟨hB₀S, isElemAbelian_map hBel _, fun B' hB'S hB'el => ?_⟩
    rw [hB₀card]
    exact hmax B' (hB'S.trans hS.1) hB'el
  have hB₀Q : B₀ = Q := hcon B₀ hB₀max
  have hBQ : B = Q := by
    have h1 : B = B₀.map (MulAut.conj h).toMonoidHom := by
      rw [hB₀, Subgroup.map_map]
      ext x
      simp [mul_assoc]
    rw [h1, hB₀Q, map_conj_eq_of_mem_normalizer (hGQ hhG)]
  apply Subgroup.map_injective R₀.subtype_injective
  rw [← hBdef, hBQ, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQR]

omit [Finite G] in
theorem card_eq_card_inf_mul_card_map [Finite G] {H : Type} [Group H] {A Q L : Subgroup G}
    (hAL : A ≤ L) (f : ↥L →* H) (hf : ∀ a : ↥L, f a = 1 ↔ (a : G) ∈ Q) :
    Nat.card A = Nat.card ↥(A ⊓ Q) * Nat.card ↥((A.subgroupOf L).map f) := by
  set φ := f.comp (A.subgroupOf L).subtype with hφ
  have hrange : φ.range = (A.subgroupOf L).map f := by
    rw [hφ, MonoidHom.range_comp, Subgroup.range_subtype]
  have h1 : Nat.card ↥(A.subgroupOf L) = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv,
      Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker, mul_comm]
  have h2 : Nat.card φ.ker = Nat.card ↥(A ⊓ Q) := by
    refine le_antisymm (Nat.card_le_card_of_injective
      (fun x : ↥φ.ker => (⟨(((x : ↥(A.subgroupOf L)) : ↥L) : G), (x : ↥(A.subgroupOf L)).2,
        (hf _).mp x.2⟩ : ↥(A ⊓ Q)))
      fun x y hxy => Subtype.ext (Subtype.ext (Subtype.ext
        (congrArg (fun z : ↥(A ⊓ Q) => (z : G)) hxy))))
      (Nat.card_le_card_of_injective
        (fun y : ↥(A ⊓ Q) => (⟨⟨⟨y, hAL y.2.1⟩, y.2.1⟩, (hf _).mpr y.2.2⟩ : ↥φ.ker))
        fun x y hxy => Subtype.ext
          (congrArg (fun z : ↥φ.ker => (((z : ↥(A.subgroupOf L)) : ↥L) : G)) hxy))
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, h1, h2, hrange]

section Unique

variable {L Q : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
  {α : ↥L →* ↥(StatedSL 3 F)}

theorem eq_of_offenders_c136 (hα : IsModO2Surj L α) (hQO : pCoreOf 2 L = Q)
    (β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F))
    (hβ : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i))
    {S A₁ A₂ : Subgroup G} (hS2 : IsPGroup 2 S) (hA₁ : A₁ ≤ S ⊓ L) (hA₂ : A₂ ≤ S ⊓ L)
    (hel₁ : IsElemAbelian 2 A₁) (hel₂ : IsElemAbelian 2 A₂)
    (hcard₁ : Nat.card A₁ = Nat.card F ^ 6) (hcard₂ : Nat.card A₂ = Nat.card F ^ 6)
    (hi₁ : Nat.card ↥(A₁ ⊓ Q) = Nat.card F ^ 4) (hi₂ : Nat.card ↥(A₂ ⊓ Q) = Nat.card F ^ 4)
    (hc₁ : Nat.card ↥(Q ⊓ Subgroup.centralizer (A₁ : Set G)) = Nat.card F ^ 4)
    (hc₂ : Nat.card ↥(Q ⊓ Subgroup.centralizer (A₂ : Set G)) = Nat.card F ^ 4) : A₁ = A₂ := by
  classical
  set q := Nat.card F with hq
  have hq0 : 0 < q := Nat.card_pos
  let e₀ := specialLinearGroupEquivStatedSL 3 F
  let α' : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F := e₀.symm.toMonoidHom.comp α
  have hα'mat : ∀ a, ((α' a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := fun a => by
    have h1 := specialLinearGroupEquivStatedSL_coe 3 F (e₀.symm (α a))
    rw [MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  have hker' : ∀ a : ↥L, α' a = 1 ↔ (a : G) ∈ Q := by
    intro a
    rw [← hQO, mem_pCoreOf_iff', ← hα.2, MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 := congrArg e₀ h
      simpa [α'] using h1
    · intro h
      simp [α', h]
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hQO]
    exact le_normalizer_pCoreOf 2 L
  have hP2 : IsPGroup 2 (((S ⊓ L).subgroupOf L).map α') := by
    refine IsPGroup.map (fun x => ?_) α'
    obtain ⟨k, hk⟩ := hS2 ⟨_, x.2.1⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h1 := congrArg Subtype.val hk
    simpa using h1
  obtain ⟨g, hg⟩ := exists_conj_unitriangular_of_isPGroup hP2
  let αg : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F := (MulAut.conj g⁻¹).toMonoidHom.comp α'
  have hαg : ∀ a, αg a = g⁻¹ * α' a * g := fun a => by
    simp [αg]
  have hU : ∀ a : ↥L, (a : G) ∈ S → αg a ∈ unitriangular 3 F := by
    intro a ha
    rw [hαg]
    exact hg _ ⟨a, ⟨ha, a.2⟩, rfl⟩
  have hkerg : ∀ a : ↥L, αg a = 1 ↔ (a : G) ∈ Q := by
    intro a
    rw [← hker', hαg]
    constructor
    · intro h
      calc α' a = g * (g⁻¹ * α' a * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
    · intro h
      rw [h]
      group
  let cg : ↥Q → Fin 2 → Fin 3 → F := fun u k =>
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (crd β u k)
  have hcgk : ∀ u k, cg u k =
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (crd β u k) := fun _ _ => rfl
  have hgg : ((g : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hcg_mul : ∀ u u', cg (u * u') = cg u + cg u' := by
    intro u u'
    funext k
    simp only [cg, crd_mul, Pi.add_apply, Matrix.mulVec_add]
  have hcg_inj : Function.Injective cg := by
    intro u u' h
    apply crd_injective β
    funext k
    have h1 := congrArg (fun v => ((g : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).mulVec (v k)) h
    simp only [cg, Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec] at h1
    exact h1
  have hcg_surj : ∀ v, ∃ u, cg u = v := by
    intro v
    refine ⟨elt β fun k => ((g : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F).mulVec (v k), ?_⟩
    funext k
    simp only [cg, crd_elt, Matrix.mulVec_mulVec]
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one,
      Matrix.one_mulVec]
  have hcg_conj : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ k,
      cg v k = ((αg a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
        (cg u k) := by
    intro a u v huv k
    have h1 := hβ a u v huv k
    rw [hcgk, hcgk, hαg, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, hgg, Matrix.mul_one,
      ← Matrix.mulVec_mulVec, hα'mat]
    exact congrArg _ h1
  have hcent : ∀ {A : Subgroup G}, A ≤ L → ∀ u : ↥Q,
      (u : G) ∈ Subgroup.centralizer (A : Set G) ↔ ∀ a : ↥L, (a : G) ∈ A → ∀ k,
        ((αg a : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (cg u k) = cg u k := by
    intro A hAL u
    constructor
    · intro hu a ha k
      have hmem : (a : G) * u * (a : G)⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hLQ a.2) _).mp u.2
      have h1 := hcg_conj a u ⟨_, hmem⟩ rfl k
      have hval : (⟨_, hmem⟩ : ↥Q) = u := by
        apply Subtype.ext
        show (a : G) * u * (a : G)⁻¹ = u
        rw [Subgroup.mem_centralizer_iff.mp hu _ ha]
        group
      rw [← h1, hval]
    · intro h
      refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
      have haL : a ∈ L := hAL ha
      have hmem : a * (u : G) * a⁻¹ ∈ Q :=
        (Subgroup.mem_normalizer_iff.mp (hLQ haL) _).mp u.2
      have h1 : cg ⟨_, hmem⟩ = cg u := by
        funext k
        rw [hcg_conj ⟨a, haL⟩ u ⟨_, hmem⟩ rfl k]
        exact h ⟨a, haL⟩ ha k
      have h2 : a * (u : G) * a⁻¹ = u := congrArg Subtype.val (hcg_inj h1)
      calc a * (u : G) = a * u * a⁻¹ * a := by group
        _ = u * a := by rw [h2]
  have hA₁L : A₁ ≤ L := fun x hx => (hA₁ hx).2
  have hA₂L : A₂ ≤ L := fun x hx => (hA₂ hx).2
  set E₁ := (A₁.subgroupOf L).map αg with hE₁
  set E₂ := (A₂.subgroupOf L).map αg with hE₂
  have hEcard : ∀ {A : Subgroup G}, A ≤ L → Nat.card A = q ^ 6 → Nat.card ↥(A ⊓ Q) = q ^ 4 →
      Nat.card ↥((A.subgroupOf L).map αg) = q ^ 2 := by
    intro A hAL hA hAQ
    have h1 := card_eq_card_inf_mul_card_map hAL αg hkerg
    rw [hA, hAQ] at h1
    have h2 : q ^ 4 * q ^ 2 = q ^ 6 := by ring
    exact (Nat.eq_of_mul_eq_mul_left (pow_pos hq0 4) (h1.symm.trans h2.symm))
  have hE₁card := hEcard hA₁L hcard₁ hi₁
  have hE₂card := hEcard hA₂L hcard₂ hi₂
  have hEU : ∀ {A : Subgroup G}, A ≤ S ⊓ L → (A.subgroupOf L).map αg ≤ unitriangular 3 F := by
    intro A hA
    rintro _ ⟨a, ha, rfl⟩
    exact hU a (hA ha).1
  have hEel : ∀ {A : Subgroup G}, IsElemAbelian 2 A →
      (∀ x ∈ (A.subgroupOf L).map αg, ∀ y ∈ (A.subgroupOf L).map αg, x * y = y * x) ∧
        ∀ x ∈ (A.subgroupOf L).map αg, x * x = 1 := by
    intro A hA
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact congrArg (fun z : ↥A => (z : G)) (hA.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      have h1 : a * a = 1 := by
        apply Subtype.ext
        have := hA.2 _ ha
        rw [sq] at this
        exact this
      rw [h1, map_one]
  have hfix : ∀ {A : Subgroup G}, A ≤ L →
      Nat.card ↥(Q ⊓ Subgroup.centralizer (A : Set G)) = q ^ 4 →
      Nat.card (slFix ((A.subgroupOf L).map αg)) = q ^ 2 := by
    intro A hAL hA
    have h1 : Nat.card ↥(Q ⊓ Subgroup.centralizer (A : Set G)) =
        Nat.card {v : Fin 2 → Fin 3 → F // ∀ k, v k ∈ slFix ((A.subgroupOf L).map αg)} := by
      refine le_antisymm (Nat.card_le_card_of_injective
        (fun u : ↥(Q ⊓ Subgroup.centralizer (A : Set G)) => ⟨cg ⟨u, u.2.1⟩, fun k => ?_⟩)
        fun x y hxy => ?_) (Nat.card_le_card_of_injective
        (fun v => ⟨(hcg_surj v.1).choose, (hcg_surj v.1).choose.2, ?_⟩) fun x y hxy => ?_)
      · rintro _ ⟨a, ha, rfl⟩
        exact (hcent hAL ⟨u, u.2.1⟩).mp u.2.2 a ha k
      · have h2 := hcg_inj (congrArg (fun z : {v : Fin 2 → Fin 3 → F //
          ∀ k, v k ∈ slFix ((A.subgroupOf L).map αg)} => z.1) hxy)
        exact Subtype.ext (congrArg (fun z : ↥Q => (z : G)) h2)
      · refine (hcent hAL _).mpr fun a ha k => ?_
        rw [(hcg_surj v.1).choose_spec]
        exact (mem_slFix.mp (v.2 k)) _ ⟨a, ha, rfl⟩
      · have h2 := congrArg (fun z : ↥(Q ⊓ Subgroup.centralizer (A : Set G)) => (z : G)) hxy
        have h3 : (hcg_surj x.1).choose = (hcg_surj y.1).choose := Subtype.ext h2
        have h4 := congrArg cg h3
        rw [(hcg_surj x.1).choose_spec, (hcg_surj y.1).choose_spec] at h4
        exact Subtype.ext h4
    rw [h1, card_pairs_mem] at hA
    have h2 : (q ^ 2) ^ 2 = q ^ 4 := by ring
    exact Nat.pow_left_injective two_ne_zero (hA.trans h2.symm)
  have hE₁fix := hfix hA₁L hc₁
  have hE₂fix := hfix hA₂L hc₂
  have hC₁ := col_of_card (hEU hA₁) (hEel hel₁).1 (hEel hel₁).2 hE₁card hE₁fix.ge
  have hC₂ := col_of_card (hEU hA₂) (hEel hel₂).1 (hEel hel₂).2 hE₂card hE₂fix.ge
  have hE : E₁ = E₂ := eq_of_col_of_card (hEU hA₁) (hEU hA₂) hC₁ hC₂ hE₁card hE₂card
  have hCQ₁ : Q ⊓ Subgroup.centralizer (A₁ : Set G) ≤ A₁ := by
    have hle : A₁ ⊓ Q ≤ Q ⊓ Subgroup.centralizer (A₁ : Set G) := fun x hx =>
      ⟨hx.2, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        congrArg Subtype.val (hel₁.1.is_comm.comm ⟨y, hy⟩ ⟨x, hx.1⟩)⟩
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hi₁, hc₁])
    rw [← heq]
    exact inf_le_left
  have hpar : ∀ a' : ↥A₂, ∃ a : ↥A₁, αg ⟨a, hA₁L a.2⟩ = αg ⟨a', hA₂L a'.2⟩ := by
    intro a'
    have h1 : αg ⟨a', hA₂L a'.2⟩ ∈ E₁ := by
      rw [hE]
      exact ⟨⟨a', hA₂L a'.2⟩, a'.2, rfl⟩
    obtain ⟨b, hb, hbe⟩ := h1
    exact ⟨⟨b, hb⟩, hbe⟩
  choose par hpar using hpar
  have hqmem : ∀ a' : ↥A₂, ((par a' : G))⁻¹ * a' ∈ Q := by
    intro a'
    have h1 : αg (⟨par a', hA₁L (par a').2⟩⁻¹ * ⟨a', hA₂L a'.2⟩) = 1 := by
      rw [map_mul, map_inv, hpar, inv_mul_cancel]
    exact (hkerg _).mp h1
  let w : ↥A₂ → Fin 2 → Fin 3 → F := fun a' => cg ⟨_, hqmem a'⟩
  have hinvol : ∀ {A : Subgroup G}, IsElemAbelian 2 A → ∀ x ∈ A, x⁻¹ = x := by
    intro A hA x hx
    have h1 := hA.2 x hx
    rw [sq] at h1
    exact inv_eq_of_mul_eq_one_right h1
  have hrel : ∀ (a'₁ a'₂ : ↥A₂) (k : Fin 2),
      ((αg ⟨a'₂, hA₂L a'₂.2⟩ : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).mulVec (w a'₁ k) - w a'₁ k =
        ((αg ⟨a'₁, hA₂L a'₁.2⟩ : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).mulVec (w a'₂ k) - w a'₂ k := by
    intro a'₁ a'₂ k
    set b₁ : G := ((par a'₁ : ↥A₁) : G)
    set b₂ : G := ((par a'₂ : ↥A₁) : G)
    set q₁ : G := b₁⁻¹ * a'₁ with hq₁
    set q₂ : G := b₂⁻¹ * a'₂ with hq₂
    have hb₁₂ : b₁ * b₂ = b₂ * b₁ :=
      congrArg Subtype.val (hel₁.1.is_comm.comm (par a'₁) (par a'₂))
    have ha₁₂ : (a'₁ : G) * a'₂ = a'₂ * a'₁ :=
      congrArg Subtype.val (hel₂.1.is_comm.comm a'₁ a'₂)
    have hkey : (b₂⁻¹ * q₁ * b₂) * q₂ = (b₁⁻¹ * q₂ * b₁) * q₁ := by
      have h1 : (a'₁ : G) = b₁ * q₁ := by rw [hq₁]; group
      have h2 : (a'₂ : G) = b₂ * q₂ := by rw [hq₂]; group
      have h3 : b₁ * q₁ * (b₂ * q₂) = b₂ * q₂ * (b₁ * q₁) := by rw [← h1, ← h2, ha₁₂]
      calc (b₂⁻¹ * q₁ * b₂) * q₂ = (b₁ * b₂)⁻¹ * (b₁ * q₁ * (b₂ * q₂)) := by group
        _ = (b₂ * b₁)⁻¹ * (b₂ * q₂ * (b₁ * q₁)) := by rw [h3, hb₁₂]
        _ = (b₁⁻¹ * q₂ * b₁) * q₁ := by group
    have hb₂inv : b₂⁻¹ = b₂ := hinvol hel₁ _ (par a'₂).2
    have hb₁inv : b₁⁻¹ = b₁ := hinvol hel₁ _ (par a'₁).2
    have hmem₁ : b₂⁻¹ * q₁ * b₂ ∈ Q := by
      have h2 : b₂⁻¹ * q₁ * b₂ = b₂ * q₁ * b₂⁻¹ := by rw [hb₂inv]
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp (hLQ (hA₁L (par a'₂).2)) _).mp (hqmem a'₁)
    have hmem₂ : b₁⁻¹ * q₂ * b₁ ∈ Q := by
      have h2 : b₁⁻¹ * q₂ * b₁ = b₁ * q₂ * b₁⁻¹ := by rw [hb₁inv]
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp (hLQ (hA₁L (par a'₁).2)) _).mp (hqmem a'₂)
    have hc₁' : cg ⟨_, hmem₁⟩ k = ((αg ⟨a'₂, hA₂L a'₂.2⟩ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec (w a'₁ k) := by
      rw [← hpar a'₂]
      refine hcg_conj ⟨b₂, hA₁L (par a'₂).2⟩ ⟨_, hqmem a'₁⟩ ⟨_, hmem₁⟩ ?_ k
      show b₂⁻¹ * q₁ * b₂ = b₂ * q₁ * b₂⁻¹
      rw [hb₂inv]
    have hc₂' : cg ⟨_, hmem₂⟩ k = ((αg ⟨a'₁, hA₂L a'₁.2⟩ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F).mulVec (w a'₂ k) := by
      rw [← hpar a'₁]
      refine hcg_conj ⟨b₁, hA₁L (par a'₁).2⟩ ⟨_, hqmem a'₂⟩ ⟨_, hmem₂⟩ ?_ k
      show b₁⁻¹ * q₂ * b₁ = b₁ * q₂ * b₁⁻¹
      rw [hb₁inv]
    have hsum : cg ⟨_, hmem₁⟩ + w a'₂ = cg ⟨_, hmem₂⟩ + w a'₁ := by
      rw [← hcg_mul, ← hcg_mul]
      congr 1
      exact Subtype.ext hkey
    have hk := congrFun hsum k
    simp only [Pi.add_apply] at hk
    rw [hc₁', hc₂'] at hk
    calc _ = ((αg ⟨a'₂, hA₂L a'₂.2⟩ : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F).mulVec (w a'₁ k) + w a'₂ k - w a'₂ k - w a'₁ k := by abel
      _ = _ := by rw [hk]; abel
  have hsurj₂ := surjective_col_of_card (hEU hA₂) hC₂ hE₂card
  have hw2 : ∀ (a' : ↥A₂) (k : Fin 2), w a' k 2 = 0 := by
    intro a' k
    refine coord_two_eq_zero_of_cocycle (X := fun a'' : ↥A₂ => αg ⟨a'', hA₂L a''.2⟩)
      (fun a'' => hU _ (hA₂ a''.2).1) (fun a'' => hC₂ _ ⟨_, a''.2, rfl⟩) (fun b c => ?_)
      (w := fun a'' => w a'' k) (fun i j => hrel i j k) a'
    obtain ⟨⟨_, ⟨x, hx, rfl⟩⟩, hxy⟩ := hsurj₂ (b, c)
    simp only [Prod.mk.injEq] at hxy
    exact ⟨⟨x, hx⟩, hxy⟩
  have hA₂A₁ : A₂ ≤ A₁ := by
    intro x hx
    set a' : ↥A₂ := ⟨x, hx⟩
    have hqC : ((par a' : G))⁻¹ * x ∈ Subgroup.centralizer (A₁ : Set G) := by
      refine (hcent hA₁L ⟨_, hqmem a'⟩).mpr fun a ha k => ?_
      have hmem : αg a ∈ E₂ := by
        rw [← hE]
        exact ⟨a, ha, rfl⟩
      rw [mulVec_of_col (hEU hA₂ hmem) (hC₂ _ hmem)]
      have h1 : w a' k 2 = 0 := hw2 a' k
      simp only [w] at h1
      rw [h1, zero_smul, add_zero]
    have hqA : ((par a' : G))⁻¹ * x ∈ A₁ := hCQ₁ ⟨hqmem a', hqC⟩
    have h1 : x = (par a' : G) * (((par a' : G))⁻¹ * x) := by group
    rw [h1]
    exact A₁.mul_mem (par a').2 hqA
  exact (Subgroup.eq_of_le_of_card_ge hA₂A₁ (by rw [hcard₁, hcard₂])).symm

end Unique

theorem lemmaC136_holds : LemmaC136 := by
  intro G _ _ G₀ R₀ L S n F _ _ α hMS hL hG₀ hGL hn hF hα hS hCL hN
  classical
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
  have hLG : L ≤ G₀ := le_of_mem_cComp hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hF
  obtain ⟨c, hc0, hc1, hcc⟩ := exists_good_scalar hn hF
  have hQ1 := centralizer_c134Q_eq hc0 hc1 hcc hα hLG hGL hperf two_ne_zero hN hCL
  have hQO := pCoreOf_eq_c134Q hc0 hc1 hcc hα hLG hGL hperf two_ne_zero hN hCL
  set Q := c134Q G₀ L with hQdef
  obtain ⟨-, -, β₀, hβs, hβk, hβeq⟩ := hN
  have hβinj : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let β : ↥Q ≃* Multiplicative (Fin 2 → Fin 3 → F) := MulEquiv.ofBijective β₀ ⟨hβinj, hβs⟩
  have hβ : ∀ (a : ↥L) (u v : ↥Q), (v : G) = a * u * a⁻¹ → ∀ i : Fin 2,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec
          (Multiplicative.toAdd (β u) i) := by
    intro a u v huv i
    have h := hβeq a u v huv i
    have hb : ∀ w, β w = β₀ w := fun _ => rfl
    rw [hb, hb]
    simpa [moduleAct] using h
  have hQL : Q ≤ L := c134Q_le hGL
  have hGQ : G₀ ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_c134Q hGL
  have hbound : ∀ {B : Subgroup G}, B ≤ G₀ → IsElemAbelian 2 B →
      Nat.card B ≤ Nat.card F ^ 6 ∧
        (Nat.card B = Nat.card F ^ 6 →
          B = Q ∨ (B ≤ L ∧ Nat.card ↥(B ⊓ Q) = Nat.card F ^ 4 ∧
            Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) = Nat.card F ^ 4)) :=
    fun hBG hB => card_le_of_c136 hα hLG hGL hQL hGQ hQ1 β hβ hBG hB
  have hQcard : Nat.card Q = Nat.card F ^ 6 := by
    rw [Nat.card_congr (β.toEquiv.trans Multiplicative.toAdd), card_pairs]
  have hQel : IsElemAbelian 2 Q := by
    refine ⟨⟨⟨fun x y => β.injective (by rw [map_mul, map_mul, mul_comm])⟩⟩, fun x hx => ?_⟩
    have h1 : β (⟨x, hx⟩ ^ 2) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one, two_nsmul]
      exact CharTwo.add_self_eq_zero _
    have h2 : (⟨x, hx⟩ : ↥Q) ^ 2 = 1 := β.injective (h1.trans (map_one β).symm)
    have h3 := congrArg Subtype.val h2
    simpa using h3
  have hQO2 : Q ≤ pCoreOf 2 G₀ :=
    commutator_le_left_of_le_normalizer (hLG.trans (le_normalizer_pCoreOf 2 G₀))
  have hQS : Q ≤ S := hQO2.trans (pCoreOf_two_le_of_isSylowTwoOf hS)
  have hQmax : IsMaxElemAbelian S Q :=
    ⟨hQS, hQel, fun B hBS hB => (hbound (hBS.trans hS.1) hB).1.trans hQcard.ge⟩
  have hQne : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQcard
    have h2 := two_le_card_field (F := F)
    have h3 : 2 ^ 6 ≤ Nat.card F ^ 6 := Nat.pow_le_pow_left h2 6
    omega
  obtain ⟨A, hAmax, hAQ⟩ := exists_isMaxElemAbelian_ne hMS hS hQO2 hGQ hQne hQel
    fun B hBG hB => (hbound hBG hB).1.trans hQcard.ge
  have hstruct : ∀ B : Subgroup G, IsMaxElemAbelian S B → B ≠ Q →
      B ≤ L ∧ Nat.card B = Nat.card F ^ 6 ∧ Nat.card ↥(B ⊓ Q) = Nat.card F ^ 4 ∧
        Nat.card ↥(Q ⊓ Subgroup.centralizer (B : Set G)) = Nat.card F ^ 4 := by
    intro B hB hBQ
    have hcard : Nat.card B = Nat.card F ^ 6 :=
      le_antisymm (hbound (hB.1.trans hS.1) hB.2.1).1 (hQcard ▸ hB.2.2 Q hQS hQel)
    rcases (hbound (hB.1.trans hS.1) hB.2.1).2 hcard with h | ⟨h1, h2, h3⟩
    · exact absurd h hBQ
    · exact ⟨h1, hcard, h2, h3⟩
  obtain ⟨hAL, hAcard, hAQcard, hACcard⟩ := hstruct A hAmax hAQ
  refine ⟨?_, ?_, A, hAL, hAmax, fun B hB => ?_, ?_⟩
  · rw [hQO]
    exact hQ1
  · rw [hQO]
    exact hQmax
  · rw [hQO]
    by_cases hBQ : B = Q
    · exact Or.inl hBQ
    · right
      obtain ⟨hBL, hBcard, hBQcard, hBCcard⟩ := hstruct B hB hBQ
      exact eq_of_offenders_c136 hα hQO β hβ hS.2.1 (le_inf hB.1 hBL) (le_inf hAmax.1 hAL)
        hB.2.1 hAmax.2.1 hBcard hAcard hBQcard hAQcard hBCcard hACcard
  · rw [hQO, hAQcard, Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm]

end CFSG.Quasithin.H13.Ch4
