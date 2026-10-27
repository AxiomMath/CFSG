module

public import CFSG.Quasithin.Vol2.KGFactC31M24Oct
public import CFSG.Quasithin.Vol2.KGFactC31M24Sx
public import CFSG.Quasithin.Vol2.KGFactC31M24Ex
public import CFSG.Quasithin.Vol2.KGFactC31M24Frame

public section

namespace CFSG.Quasithin.KGC31.M24

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.KGC31 _root_.Certificates

variable {A : Type} [Group A] [Finite A] {S M₀ R M V : Subgroup A}

theorem R_eq_of_cent_le (h : Setup S M₀ R M V) {U : Subgroup A} (hUV : U ≤ V)
    (hCU : Subgroup.centralizer (U : Set A) ≤ U) : R = U ∧ V = U := by
  have h1 : R ≤ U := h.hRC.trans ((Subgroup.centralizer_le hUV).trans hCU)
  exact ⟨le_antisymm h1 (hUV.trans h.hVR), le_antisymm (h.hVR.trans h1) hUV⟩

theorem R_eq_of_cent_comm (h : Setup S M₀ R M V) {U : Subgroup A} (hUV : U ≤ V)
    (hab : ∀ a ∈ Subgroup.centralizer (U : Set A), ∀ b ∈ Subgroup.centralizer (U : Set A),
      a * b = b * a)
    (h2 : IsPGroup 2 ↥(Subgroup.centralizer (U : Set A))) :
    R = Subgroup.centralizer (U : Set A) := by
  have hVC : V ≤ Subgroup.centralizer (U : Set A) :=
    h.V_le_cent.trans (Subgroup.centralizer_le hUV)
  have hCV := centralizer_eq_of_comm hUV hVC hab
  rw [← hCV]
  exact eq_centralizer_of_isPGroup h.hMN h.hM₀V h.hsyl h.hNR h.hRC (hCV ▸ h2)

omit [Finite A] in
theorem not_mem_of_odd {R : Subgroup A} (hR2 : IsPGroup 2 ↥R) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) {y : A} (hyk : ∃ k, y ^ p ^ k = 1) (hy1 : y ≠ 1) : y ∉ R := by
  intro hyR
  obtain ⟨n, hn⟩ := hR2 ⟨y, hyR⟩
  obtain ⟨k, hk⟩ := hyk
  have h2 : y ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hco : Nat.Coprime (2 ^ n) (p ^ k) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega))
  have h1 := Nat.eq_one_of_dvd_coprimes hco (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one hk)
  exact hy1 (orderOf_eq_one_iff.mp h1)

omit [Finite A] in
theorem cent_map {f : G₀ →* A} (hf : Iso f) {k : ℕ} {v : Fin k → G₀} (hv : EBasis v)
    {X : Subgroup G₀} (hX : Subgroup.centralizer (eSub hv : Set G₀) = X) :
    Subgroup.centralizer (((eSub hv).map f : Subgroup A) : Set A) = X.map f := by
  rw [← hf.map_centralizer, hX]

omit [Finite A] in
theorem eSub_map_facts {f : G₀ →* A} (hf : Iso f) {k : ℕ} {v : Fin k → G₀} (hv : EBasis v) :
    (∀ a ∈ (eSub hv).map f, ∀ b ∈ (eSub hv).map f, a * b = b * a) ∧
      IsPGroup 2 ↥((eSub hv).map f) := by
  refine ⟨?_, IsPGroup.of_card (n := k) (by rw [hf.card_map, card_eSub])⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul, eSub_comm hv a b ha hb]

theorem case_o (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) {y t : A} (hy : y ∈ M₀)
    (ht : t ∈ V) (hyR : y ∉ R) (hU : orbSub y t = (eSub basis_o).map f) : Concl S M₀ R M V := by
  have hUV : orbSub y t ≤ V := orbSub_le (h.hM₀V hy) ht
  rw [hU] at hUV
  have hCU := cent_map hf basis_o cent_o
  obtain ⟨hR, -⟩ := R_eq_of_cent_le h hUV hCU.le
  exact concl_octad h hf hR hy hyR

theorem case_s32 (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) {y t : A} (hy : y ∈ M₀)
    (ht : t ∈ V) (hyk : ∃ k, y ^ 5 ^ k = 1) (hy1 : y ≠ 1)
    (hU : orbSub y t = (eSub basis_s32).map f) : Concl S M₀ R M V := by
  have hUV : orbSub y t ≤ V := orbSub_le (h.hM₀V hy) ht
  rw [hU] at hUV
  have hCU := cent_map hf basis_s32 cent_s32
  obtain ⟨hab, h2⟩ := eSub_map_facts hf basis_s
  have hR := R_eq_of_cent_comm h hUV (hCU ▸ hab) (hCU ▸ h2)
  rw [hCU] at hR
  exact concl_sextet h hf hR hy hyk hy1

theorem case_s16 (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) {y t : A} (hy : y ∈ M₀)
    (ht : t ∈ V) (hyk : ∃ k, y ^ 5 ^ k = 1) (hy1 : y ≠ 1)
    (hU : orbSub y t = (eSub basis_s16).map f) : Concl S M₀ R M V := by
  have hUV : orbSub y t ≤ V := orbSub_le (h.hM₀V hy) ht
  rw [hU] at hUV
  have hCU := cent_map hf basis_s16 cent_s16
  obtain ⟨hab, h2⟩ := eSub_map_facts hf basis_s
  have hR := R_eq_of_cent_comm h hUV (hCU ▸ hab) (hCU ▸ h2)
  rw [hCU] at hR
  exact concl_sextet h hf hR hy hyk hy1

theorem case_r2 (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) {y t : A} (hy : y ∈ M₀)
    (ht : t ∈ V) (hU : orbSub y t = (eSub basis_r2).map f) : False := by
  have hUV : orbSub y t ≤ V := orbSub_le (h.hM₀V hy) ht
  rw [hU] at hUV
  have hCU := cent_map hf basis_r2 cent_r2
  obtain ⟨hR, -⟩ := R_eq_of_cent_le h hUV hCU.le
  exact false_r2 h hf hR

theorem case_u4 (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) {y t : A} (hy : y ∈ M₀)
    (ht : t ∈ V) (hU : orbSub y t = (eSub basis_u4).map f) : False := by
  have hUV : orbSub y t ≤ V := orbSub_le (h.hM₀V hy) ht
  rw [hU] at hUV
  have hCU := cent_map hf basis_u4 cent_u4
  rw [Subgroup.map_map] at hCU
  obtain ⟨hab, h2⟩ := eSub_map_facts (hf.conj d4) basis_r2
  have hab' : ∀ a ∈ Subgroup.centralizer ((((eSub basis_u4).map f : Subgroup A)) : Set A),
      ∀ b ∈ Subgroup.centralizer ((((eSub basis_u4).map f : Subgroup A)) : Set A),
        a * b = b * a := by
    rw [hCU]
    exact hab
  have h2' : IsPGroup 2
      ↥(Subgroup.centralizer ((((eSub basis_u4).map f : Subgroup A)) : Set A)) := by
    rw [hCU]
    exact h2
  have hR := R_eq_of_cent_comm h hUV hab' h2'
  rw [hCU] at hR
  exact false_r2 h (hf.conj d4) hR

theorem case_u6 (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) {y t : A} (hy : y ∈ M₀)
    (ht : t ∈ V) (hU : orbSub y t = (eSub basis_u6).map f) : False := by
  have hUV : orbSub y t ≤ V := orbSub_le (h.hM₀V hy) ht
  rw [hU] at hUV
  have hCU := cent_map hf basis_u6 cent_u6
  rw [Subgroup.map_map] at hCU
  obtain ⟨hab, h2⟩ := eSub_map_facts (hf.conj d6) basis_t
  have hab' : ∀ a ∈ Subgroup.centralizer ((((eSub basis_u6).map f : Subgroup A)) : Set A),
      ∀ b ∈ Subgroup.centralizer ((((eSub basis_u6).map f : Subgroup A)) : Set A),
        a * b = b * a := by
    rw [hCU]
    exact hab
  have h2' : IsPGroup 2
      ↥(Subgroup.centralizer ((((eSub basis_u6).map f : Subgroup A)) : Set A)) := by
    rw [hCU]
    exact h2
  have hR := R_eq_of_cent_comm h hUV hab' h2'
  rw [hCU] at hR
  exact false_rt h (hf.conj d6) hR

theorem case_frame (h : Setup S M₀ R M V) {f : G₀ →* A} (hf : Iso f) {y t : A} (hy : y ∈ M₀)
    (ht : t ∈ V) (hyk : ∃ k, y ^ 7 ^ k = 1) (hy1 : y ≠ 1) (hyR : y ∉ R)
    (hx7 : f x7 ∈ Subgroup.zpowers y) {c : G₀}
    (hframe : ∀ {v : G₀}, v ∈ Subgroup.centralizer
        (((eSub basis_u5).map (MulAut.conj c).toMonoidHom : Subgroup G₀) : Set G₀) →
      v ∉ (eSub basis_u5).map (MulAut.conj c).toMonoidHom →
      (∀ a ∈ (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v,
        ∀ b ∈ (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v, a * b = b * a) →
      (∀ a ∈ (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v, a * a = 1) →
      (∃ e : G₀, (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v =
          (eSub basis_o).map (MulAut.conj e).toMonoidHom) ∨
        ∃ e : G₀, (eSub basis_u5).map (MulAut.conj c).toMonoidHom ⊔ orbSub x7 v =
          (eSub basis_t).map (MulAut.conj e).toMonoidHom)
    (hU : orbSub y t = ((eSub basis_u5).map (MulAut.conj c).toMonoidHom).map f) :
    Concl S M₀ R M V := by
  set U₀ := (eSub basis_u5).map (MulAut.conj c).toMonoidHom with hU₀
  have hUV : U₀.map f ≤ V := hU ▸ orbSub_le (h.hM₀V hy) ht
  have hCU₀ : Subgroup.centralizer (U₀ : Set G₀) = Qg.map (MulAut.conj c).toMonoidHom := by
    rw [hU₀, centralizer_map_conj, cent_u5]
  have hCU : Subgroup.centralizer ((U₀.map f : Subgroup A) : Set A) =
      (Qg.map (MulAut.conj c).toMonoidHom).map f := by
    rw [← hf.map_centralizer, hCU₀]
  have hVC : V ≤ Subgroup.centralizer ((U₀.map f : Subgroup A) : Set A) :=
    h.V_le_cent.trans (Subgroup.centralizer_le hUV)
  by_cases hVU : V ≤ U₀.map f
  ·
    have hVeq : V = U₀.map f := le_antisymm hVU hUV
    have h2 : IsPGroup 2 ↥(Subgroup.centralizer (V : Set A)) := by
      rw [hVeq, hCU]
      refine IsPGroup.of_card (n := 7) ?_
      rw [hf.card_map, Subgroup.card_map_of_injective (MulAut.conj c).injective, card_Qg]
      norm_num
    have hR := eq_centralizer_of_isPGroup h.hMN h.hM₀V h.hsyl h.hNR h.hRC h2
    rw [hVeq, hCU, Subgroup.map_map] at hR
    rw [hU₀, Subgroup.map_map] at hVeq
    exact concl_q h (hf.conj c) hR hVeq hy hyk hy1
  ·
    obtain ⟨v, hvV, hvU⟩ := Set.not_subset.mp hVU
    obtain ⟨v₀, rfl⟩ := hf.surj v
    have hv₀C : v₀ ∈ Subgroup.centralizer (U₀ : Set G₀) := by
      have h1 := hVC hvV
      rw [← hf.map_centralizer, Subgroup.mem_map_iff_mem hf.inj] at h1
      exact h1
    have hv₀U : v₀ ∉ U₀ := fun h' => hvU ⟨v₀, h', rfl⟩
    have hx7M : f x7 ∈ M₀ := (Subgroup.zpowers_le.mpr hy) hx7
    have hWV : (U₀ ⊔ orbSub x7 v₀).map f ≤ V := by
      rw [Subgroup.map_sup, orbSub_map]
      exact sup_le hUV (orbSub_le (h.hM₀V hx7M) hvV)
    have hab : ∀ a ∈ U₀ ⊔ orbSub x7 v₀, ∀ b ∈ U₀ ⊔ orbSub x7 v₀, a * b = b * a :=
      fun a ha b hb => hf.inj (by
        rw [map_mul, map_mul]
        exact h.V_comm _ (hWV ⟨a, ha, rfl⟩) _ (hWV ⟨b, hb, rfl⟩))
    have hsq : ∀ a ∈ U₀ ⊔ orbSub x7 v₀, a * a = 1 := fun a ha => hf.inj (by
      rw [map_mul, map_one]
      have := h.hV.2 _ (hWV ⟨a, ha, rfl⟩)
      rwa [sq] at this)
    have key : ∀ {W : Subgroup A}, (U₀ ⊔ orbSub x7 v₀).map f = W →
        Subgroup.centralizer (W : Set A) = W → R = W := by
      intro W hW hCW
      rw [hW] at hWV
      exact le_antisymm (h.hRC.trans ((Subgroup.centralizer_le hWV).trans hCW.le))
        (hWV.trans h.hVR)
    rcases hframe hv₀C hv₀U hab hsq with ⟨e, he⟩ | ⟨e, he⟩
    · have hW : (U₀ ⊔ orbSub x7 v₀).map f = (eSub basis_o).map (f.comp
          (MulAut.conj e).toMonoidHom) := by
        rw [he, Subgroup.map_map]
      have hR := key hW (cent_map (hf.conj e) basis_o cent_o)
      exact concl_octad h (hf.conj e) hR hy hyR
    · have hW : (U₀ ⊔ orbSub x7 v₀).map f = (eSub basis_t).map (f.comp
          (MulAut.conj e).toMonoidHom) := by
        rw [he, Subgroup.map_map]
      have hR := key hW (cent_map (hf.conj e) basis_t cent_t)
      exact (false_rt h (hf.conj e) hR).elim

end CFSG.Quasithin.KGC31.M24

end
