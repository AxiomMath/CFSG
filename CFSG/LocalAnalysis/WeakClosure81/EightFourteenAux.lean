module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenApi

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_of_relIndex_two {P Q : Subgroup G} (h2 : P.relIndex Q = 2) {g : G}
    (hgP : g ∈ normalizer (P : Set G)) (hgQ : g ∈ normalizer (Q : Set G)) {x : G} (hx : x ∈ Q) :
    g * x * g⁻¹ * x⁻¹ ∈ P := by
  obtain ⟨a, haQ, ha⟩ := Subgroup.relIndex_eq_two_iff.mp h2
  have key : ∀ z ∈ Q, z ∉ P → z * a ∈ P := fun z hz hzP => by
    rcases ha z hz with ⟨h, _⟩ | ⟨h, _⟩
    · exact h
    · exact absurd h hzP
  have hy : g * x * g⁻¹ ∈ Q := (mem_normalizer_iff.mp hgQ x).1 hx
  by_cases hxP : x ∈ P
  · exact P.mul_mem ((mem_normalizer_iff.mp hgP x).1 hxP) (P.inv_mem hxP)
  · have hyP : g * x * g⁻¹ ∉ P := fun h => hxP ((mem_normalizer_iff.mp hgP x).2 h)
    have h1 := key x hx hxP
    have h2 := key _ hy hyP
    have heq : g * x * g⁻¹ * x⁻¹ = (g * x * g⁻¹ * a) * (x * a)⁻¹ := by group
    rw [heq]
    exact P.mul_mem h2 (P.inv_mem h1)

theorem mem_normalizer_conjClosure_of_mem_normalizers {V K : Subgroup G} {t : G}
    (htV : t ∈ normalizer (V : Set G)) (htK : t ∈ normalizer (K : Set G)) :
    t ∈ normalizer (conjClosure V K : Set G) := by
  have hS : t ∈ normalizer {x : G | ∃ h ∈ K, ∃ z ∈ V, h * z * h⁻¹ = x} := by
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨h, hh, z, hz, rfl⟩ := hn
    exact ⟨t * h * t⁻¹, (Subgroup.mem_normalizer_iff.mp htK h).1 hh,
      t * z * t⁻¹, (Subgroup.mem_normalizer_iff.mp htV z).1 hz, by group⟩
  exact Subgroup.normalizer_le_normalizer_closure _ hS

theorem mem_normalizer_centralizer_of_mem {S : Subgroup G} {t : G} (ht : t ∈ S) :
    t ∈ normalizer (centralizer (S : Set G) : Set G) := by
  have key : ∀ s ∈ S, ∀ x ∈ centralizer (S : Set G), s * x * s⁻¹ ∈ centralizer (S : Set G) := by
    intro s hs x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 : (s⁻¹ * y * s) * x = x * (s⁻¹ * y * s) :=
      Subgroup.mem_centralizer_iff.mp hx _ (S.mul_mem (S.mul_mem (S.inv_mem hs) hy) hs)
    calc y * (s * x * s⁻¹) = s * ((s⁻¹ * y * s) * x) * s⁻¹ := by group
      _ = s * (x * (s⁻¹ * y * s)) * s⁻¹ := by rw [h1]
      _ = (s * x * s⁻¹) * y := by group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨key t ht x, fun hx => by
    have := key t⁻¹ (S.inv_mem ht) _ hx
    simpa [mul_assoc] using this⟩

section Sit

variable {V H T A L K : Subgroup G} {i : ℕ}

theorem Sit813.sGrp_le_T (h : Sit813 V H T i A L K) : sGrp H T A K ≤ T :=
  sup_le Sit813.rGrp_le_T h.mem.1

theorem Sit813.sGrp_le_normalizer_K (h : Sit813 V H T i A L K) :
    sGrp H T A K ≤ normalizer (K : Set G) :=
  sup_le (fun _ ht => (Sit813.mem_rGrp_iff.mp ht).2.1) (Sit813.a_le_normalizer h)

theorem Sit813.sGrp_le_normalizer_V (h : Sit813 V H T i A L K) :
    sGrp H T A K ≤ normalizer (V : Set G) :=
  h.sGrp_le_T.trans h.le_normalizer_T

theorem Sit813.sGrp_le_normalizer_v1Grp (h : Sit813 V H T i A L K) :
    sGrp H T A K ≤ normalizer (v1Grp V H T A K : Set G) := fun t ht => by
  have h1 := h.sGrp_le_normalizer_V ht
  have h2 := mem_normalizer_centralizer_of_mem ht
  rw [Subgroup.mem_normalizer_iff] at h1 h2 ⊢
  intro x
  constructor
  · intro hx
    obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨(h1 x).1 hxV, (h2 x).1 hxC⟩
  · intro hx
    obtain ⟨hxV, hxC⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨(h1 x).2 hxV, (h2 x).2 hxC⟩

theorem Sit813.sGrp_le_normalizer_u1Grp (h : Sit813 V H T i A L K) :
    sGrp H T A K ≤ normalizer (u1Grp V H T A K : Set G) := fun _ ht =>
  mem_normalizer_conjClosure_of_mem_normalizers (h.sGrp_le_normalizer_v1Grp ht)
    (h.sGrp_le_normalizer_K ht)

theorem Sit813.a_le_sGrp : A ≤ sGrp H T A K := le_sup_right

theorem Sit813.k_le_normalizer_u1Grp : K ≤ normalizer (u1Grp V H T A K : Set G) :=
  le_normalizer_conjClosure _ K

theorem Sit813.v1Grp_le_V : v1Grp V H T A K ≤ V := inf_le_left

theorem Sit813.v1Grp_le_u1Grp : v1Grp V H T A K ≤ u1Grp V H T A K := le_conjClosure _ K

theorem Sit813.V_le_uGrp : V ≤ uGrp V K := le_conjClosure V K

theorem Sit813.u1Grp_le_uGrp : u1Grp V H T A K ≤ uGrp V K :=
  conjClosure_mono Sit813.v1Grp_le_V le_rfl

theorem Sit813.relIndex_v1Grp (h : Sit813 V H T i A L K)
    (h4 : Nat.card (v1Grp V H T A K) = 4) : (v1Grp V H T A K).relIndex V = 2 := by
  have e := Subgroup.relIndex_mul_card (H := v1Grp V H T A K) (K := V)
  rw [inf_of_le_left Sit813.v1Grp_le_V, h4, h.card_V_eq_eight] at e
  omega

theorem Sit813.exists_mem_K_not_mem_normalizer (h : Sit813 V H T i A L K) :
    ∃ k ∈ K, k ∉ normalizer (V : Set G) := by
  by_contra hno
  push Not at hno
  have h1 : (K ⊓ normalizer (V : Set G)).relIndex K = 1 :=
    Subgroup.relIndex_eq_one.mpr fun k hk => Subgroup.mem_inf.mpr ⟨hk, hno k hk⟩
  rw [h.concl813.d_index] at h1
  norm_num at h1

theorem Sit813.eq_one_of_centralizes_K (h : Sit813 V H T i A L K) {v : G} (hv : v ∈ V)
    (hc : ∀ k ∈ K, k * v = v * k) : v = 1 := by
  obtain ⟨k, hk, hkV⟩ := h.exists_mem_K_not_mem_normalizer
  refine h.isTI_form k hkV v hv ?_
  have : k * v * k⁻¹ = v := by rw [hc k hk]; group
  rw [this]
  exact hv

theorem Sit813.card_V_mul_card_V_le (h : Sit813 V H T i A L K) :
    Nat.card V * Nat.card V ≤ Nat.card (uGrp V K) := by
  obtain ⟨k, hk, hkV⟩ := h.exists_mem_K_not_mem_normalizer
  have hmem : ∀ v w : ↥V, (v : G) * (k * (w : G) * k⁻¹) ∈ uGrp V K := fun v w =>
    (uGrp V K).mul_mem (Sit813.V_le_uGrp v.2) (mem_conjClosure hk w.2)
  let f : ↥V × ↥V → ↥(uGrp V K) := fun p => ⟨(p.1 : G) * (k * (p.2 : G) * k⁻¹), hmem p.1 p.2⟩
  have hinj : Function.Injective f := by
    rintro ⟨v, w⟩ ⟨v', w'⟩ hf
    have hf' : (v : G) * (k * (w : G) * k⁻¹) = (v' : G) * (k * (w' : G) * k⁻¹) :=
      congrArg Subtype.val hf
    have h1 : k * ((w' : G) * (w : G)⁻¹) * k⁻¹ = (v' : G)⁻¹ * (v : G) := by
      have : (v' : G)⁻¹ * (v : G) = (k * (w' : G) * k⁻¹) * (k * (w : G) * k⁻¹)⁻¹ := by
        calc (v' : G)⁻¹ * (v : G)
            = (v' : G)⁻¹ * ((v : G) * (k * (w : G) * k⁻¹)) * (k * (w : G) * k⁻¹)⁻¹ := by group
          _ = (v' : G)⁻¹ * ((v' : G) * (k * (w' : G) * k⁻¹)) * (k * (w : G) * k⁻¹)⁻¹ := by
            rw [hf']
          _ = _ := by group
      rw [this]
      group
    have h2 : (w' : G) * (w : G)⁻¹ = 1 := by
      refine h.isTI_form k hkV _ (V.mul_mem w'.2 (V.inv_mem w.2)) ?_
      rw [h1]
      exact V.mul_mem (V.inv_mem v'.2) v.2
    have hww : w = w' := by
      apply Subtype.ext
      have : (w' : G) = (w : G) := by
        calc (w' : G) = ((w' : G) * (w : G)⁻¹) * (w : G) := by group
          _ = (w : G) := by rw [h2]; group
      exact this.symm
    subst hww
    have hvv : v = v' := by
      apply Subtype.ext
      have h3 := mul_right_cancel hf'
      exact h3
    rw [hvv]
  have := Nat.card_le_card_of_injective f hinj
  simpa [Nat.card_prod] using this

end Sit

theorem exists_mul_of_mem_sup_of_comm {P Q : Subgroup G} (hc : ∀ x ∈ P, ∀ y ∈ Q, x * y = y * x)
    {u : G} (hu : u ∈ P ⊔ Q) : ∃ x ∈ P, ∃ y ∈ Q, x * y = u := by
  have hle : P ≤ normalizer (Q : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : x * y * x⁻¹ = y := by rw [hc x hx y hy]; group
      rw [this]
      exact hy
    · intro hy
      have h1 : x⁻¹ * (x * y * x⁻¹) = (x * y * x⁻¹) * x⁻¹ := hc x⁻¹ (P.inv_mem hx) _ hy
      have h2 : x * y * x⁻¹ = y := by
        have h3 : y = x⁻¹ * (x * y * x⁻¹) * x := by group
        calc x * y * x⁻¹ = (x * y * x⁻¹ * x⁻¹) * x := by group
          _ = x⁻¹ * (x * y * x⁻¹) * x := by rw [← h1]
          _ = y := h3.symm
      rw [← h2]
      exact hy
  have hu' : u ∈ ((P ⊔ Q : Subgroup G) : Set G) := hu
  rw [Subgroup.coe_mul_of_left_le_normalizer_right P Q hle] at hu'
  obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_mul.mp hu'
  exact ⟨x, hx, y, hy, rfl⟩

theorem sl2_exists_mulVec_eq {F : Type*} [Field F] {v w : Fin 2 → F} (hv : v ≠ 0) (hw : w ≠ 0) :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec v = w := by
  have key : ∀ {v : Fin 2 → F}, v ≠ 0 → ∃ g : Matrix.SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec v = ![1, 0] := by
    intro v hv
    by_cases h0 : v 0 = 0
    · have h1 : v 1 ≠ 0 := by
        intro h1
        apply hv
        ext i
        fin_cases i <;> simp [h0, h1]
      refine ⟨⟨!![0, (v 1)⁻¹; -(v 1), 0], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_two_of, h1]
      · ext i
        fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
    · refine ⟨⟨!![(v 0)⁻¹, 0; -(v 1), v 0], ?_⟩, ?_⟩
      · simp [Matrix.det_fin_two_of, h0]
      · ext i
        fin_cases i
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
        · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
          ring
  obtain ⟨g₁, h₁⟩ := key hv
  obtain ⟨g₂, h₂⟩ := key hw
  refine ⟨g₂⁻¹ * g₁, ?_⟩
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h₁, ← h₂,
    Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem IsNaturalSL2Module.card_eq_sixteen {K U D : Subgroup G} (hnat : IsNaturalSL2Module K U D)
    (hD : ∀ u ∈ U, u ∈ D → u = 1) : Nat.card ↥U = 16 := by
  obtain ⟨F, hF, hFfin, hcard, φ, ψ, hφ, hψ, hker, heq⟩ := hnat
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (hD u u.2 ((hker u).mp hu))
  have e : ↥U ≃ Multiplicative (Fin 2 → F) := Equiv.ofBijective ψ ⟨hinj, hψ⟩
  rw [Nat.card_congr e]
  have h1 : Nat.card (Multiplicative (Fin 2 → F)) = Nat.card (Fin 2 → F) :=
    Nat.card_congr Multiplicative.toAdd
  rw [h1, Nat.card_fun, hcard]
  simp

theorem IsNaturalSL2Module.fifteen_le_ncard_orbit {K U D : Subgroup G}
    (hnat : IsNaturalSL2Module K U D) (hKU : K ≤ normalizer (U : Set G)) {u : G} (hu : u ∈ U)
    (huD : u ∉ D) : 15 ≤ Set.ncard {x : G | ∃ k ∈ K, x = k * u * k⁻¹} := by
  obtain ⟨F, hF, hFfin, hcard, φ, ψ, hφ, hψ, hker, heq⟩ := hnat
  classical
  set a : Fin 2 → F := Multiplicative.toAdd (ψ ⟨u, hu⟩) with ha
  have ha0 : a ≠ 0 := by
    intro h0
    have h1 : ψ ⟨u, hu⟩ = 1 := by simpa [ha] using h0
    exact huD ((hker ⟨u, hu⟩).mp h1)
  set orb : Set G := {x : G | ∃ k ∈ K, x = k * u * k⁻¹} with horb
  let ψ' : G → (Fin 2 → F) := fun x => if hx : x ∈ U then Multiplicative.toAdd (ψ ⟨x, hx⟩) else 0
  have hsurj : {w : Fin 2 → F | w ≠ 0} ⊆ ψ' '' orb := by
    intro w hw
    obtain ⟨g, hg⟩ := sl2_exists_mulVec_eq ha0 hw
    obtain ⟨k, hk⟩ := hφ g
    have hkU : (k : G) * u * (k : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).1 hu
    refine ⟨(k : G) * u * (k : G)⁻¹, ⟨k, k.2, rfl⟩, ?_⟩
    simp only [ψ', dif_pos hkU]
    rw [heq k ⟨u, hu⟩ ⟨(k : G) * u * (k : G)⁻¹, hkU⟩ rfl, hk]
    exact hg
  have hfin : orb.Finite := Set.toFinite _
  have hcnt : Set.ncard {w : Fin 2 → F | w ≠ 0} = 15 := by
    have h1 : {w : Fin 2 → F | w ≠ 0} = Set.univ \ {0} := by
      ext w; simp
    rw [h1, Set.ncard_diff_singleton_of_mem (Set.mem_univ _), Set.ncard_univ, Nat.card_fun,
      hcard]
    simp
  calc 15 = Set.ncard {w : Fin 2 → F | w ≠ 0} := hcnt.symm
    _ ≤ Set.ncard (ψ' '' orb) := Set.ncard_le_ncard hsurj (hfin.image _)
    _ ≤ Set.ncard orb := Set.ncard_image_le hfin

end CFSG.LocalAnalysis.WeakClosure81

end
