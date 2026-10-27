module

public import CFSG.Quasithin.EmptyFaithful.S143Setting
public import CFSG.Quasithin.Vol2.Ch12Sec8Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

variable {G : Type} [Group G]

theorem mk_eq_one_iff_mem_pCoreOf' {K : Subgroup G} (k : ↥K) :
    (QuotientGroup.mk k : OTwoQuot K) = 1 ↔ (k : G) ∈ pCoreOf 2 K := by
  rw [QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨k, h, rfl⟩
  · rintro ⟨y, hy, hyk⟩
    have : y = k := Subtype.ext hyk
    exact this ▸ hy

variable {K A : Subgroup G}

theorem IsA6Block.conj_mem (h : IsA6Block K A) {k a : G} (hk : k ∈ K) (ha : a ∈ A) :
    k * a * k⁻¹ ∈ A := by
  obtain ⟨-, hAK, -⟩ := h
  rw [hAK] at ha ⊢
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) a).mp ha

theorem IsA6Block.le (h : IsA6Block K A) : A ≤ K := by
  rw [h.2.1]
  exact pCoreOf_le 2 K

theorem IsA6Block.mul_self (h : IsA6Block K A) {a : G} (ha : a ∈ A) : a * a = 1 := by
  obtain ⟨-, -, φ, ψ, -⟩ := h
  have h1 : ψ ⟨a, ha⟩ * ψ ⟨a, ha⟩ = 1 := n6_mul_self _
  have : ψ (⟨a, ha⟩ * ⟨a, ha⟩) = ψ 1 := by rw [map_mul, h1, map_one]
  have h2 := ψ.injective this
  exact congrArg Subtype.val h2

theorem IsA6Block.exists_conj_of_ne_one (h : IsA6Block K A) {a b : G} (ha : a ∈ A) (hb : b ∈ A)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) : ∃ k ∈ K, k * a * k⁻¹ = b := by
  have hh := h
  obtain ⟨-, -, φ, ψ, hψ⟩ := hh
  have hψa : ψ ⟨a, ha⟩ ≠ 1 := fun h1 => ha1 (by
    have := ψ.injective (h1.trans (map_one ψ).symm)
    exact congrArg Subtype.val this)
  have hψb : ψ ⟨b, hb⟩ ≠ 1 := fun h1 => hb1 (by
    have := ψ.injective (h1.trans (map_one ψ).symm)
    exact congrArg Subtype.val this)
  obtain ⟨σ, hσ, hσab⟩ := n6_transitive _ _ hψa hψb
  obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (φ.symm ⟨σ, hσ⟩)
  have hkφ : φ (QuotientGroup.mk k) = ⟨σ, hσ⟩ := by rw [hk]; simp
  have hconj : (k : G) * a * (k : G)⁻¹ ∈ A := h.conj_mem k.2 ha
  refine ⟨k, k.2, ?_⟩
  have h1 := hψ k ⟨a, ha⟩ hconj
  rw [hkφ] at h1
  have h2 : ψ ⟨(k : G) * a * (k : G)⁻¹, hconj⟩ = ψ ⟨b, hb⟩ := by
    rw [h1]
    exact hσab
  exact congrArg Subtype.val (ψ.injective h2)

theorem IsA6Block.exists_conj_involution (h : IsA6Block K A) {r e : G} (hr : r ∈ K) (he : e ∈ K)
    (hrA : r ∉ A) (heA : e ∉ A) (hr2 : r * r = 1) (he2 : e * e = 1) :
    ∃ k ∈ K, ∃ b ∈ A, k * r * k⁻¹ = b * e * b⁻¹ := by
  have hh := h
  obtain ⟨-, hAK, φ, ψ, hψ⟩ := hh
  set qr : OTwoQuot K := QuotientGroup.mk ⟨r, hr⟩ with hqr
  set qe : OTwoQuot K := QuotientGroup.mk ⟨e, he⟩ with hqe
  have hqr1 : qr ≠ 1 := fun h1 => hrA (by
    rw [hAK]; exact (mk_eq_one_iff_mem_pCoreOf' ⟨r, hr⟩).mp h1)
  have hqe1 : qe ≠ 1 := fun h1 => heA (by
    rw [hAK]; exact (mk_eq_one_iff_mem_pCoreOf' ⟨e, he⟩).mp h1)
  have hqr2 : qr * qr = 1 := by
    rw [hqr, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext hr2
  have hqe2 : qe * qe = 1 := by
    rw [hqe, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_one]
    congr 1
    exact Subtype.ext he2
  set σr := φ qr with hσr
  set σe := φ qe with hσe
  have hσr1 : (σr : Equiv.Perm (Fin 6)) ≠ 1 := fun h1 => hqr1 (φ.injective (Subtype.ext (by
    rw [← hσr, h1]; simp)))
  have hσe1 : (σe : Equiv.Perm (Fin 6)) ≠ 1 := fun h1 => hqe1 (φ.injective (Subtype.ext (by
    rw [← hσe, h1]; simp)))
  have hσr2 : (σr : Equiv.Perm (Fin 6)) * σr = 1 := by
    have := congrArg (fun q => (φ q : Equiv.Perm (Fin 6))) hqr2
    simpa [map_mul] using this
  have hσe2 : (σe : Equiv.Perm (Fin 6)) * σe = 1 := by
    have := congrArg (fun q => (φ q : Equiv.Perm (Fin 6))) hqe2
    simpa [map_mul] using this
  obtain ⟨ρ, hρ, hρσ⟩ := alt6_invol_conj _ _ σr.2 σe.2 hσr1 hσe1 hσr2 hσe2
  obtain ⟨k₀, hk₀⟩ := QuotientGroup.mk_surjective (φ.symm ⟨ρ, hρ⟩)
  have hk₀φ : φ (QuotientGroup.mk k₀) = ⟨ρ, hρ⟩ := by rw [hk₀]; simp
  have himg : (QuotientGroup.mk (k₀ * ⟨r, hr⟩ * k₀⁻¹) : OTwoQuot K) = qe := by
    apply φ.injective
    apply Subtype.ext
    have e1 : (QuotientGroup.mk (k₀ * ⟨r, hr⟩ * k₀⁻¹) : OTwoQuot K) =
        QuotientGroup.mk k₀ * qr * (QuotientGroup.mk k₀)⁻¹ := by
      simp [hqr]
    rw [e1, map_mul, map_mul, map_inv, hk₀φ]
    simpa [hσr] using hρσ
  have hmem := QuotientGroup.eq.mp himg
  have hc₁ : ((k₀ * ⟨r, hr⟩ * k₀⁻¹)⁻¹ * ⟨e, he⟩ : ↥K) ∈ CFSG.Open.pCore 2 ↥K := hmem
  have hc₁A : (((k₀ * ⟨r, hr⟩ * k₀⁻¹)⁻¹ * ⟨e, he⟩ : ↥K) : G) ∈ A := by
    rw [hAK]
    exact ⟨_, hc₁, rfl⟩
  set y : G := (k₀ : G) * r * (k₀ : G)⁻¹ with hy
  have hyK : y ∈ K := K.mul_mem (K.mul_mem k₀.2 hr) (K.inv_mem k₀.2)
  have hy2 : y * y = 1 := by
    rw [hy]
    calc (k₀ : G) * r * (k₀ : G)⁻¹ * ((k₀ : G) * r * (k₀ : G)⁻¹) =
        (k₀ : G) * (r * r) * (k₀ : G)⁻¹ := by group
      _ = 1 := by rw [hr2]; group
  have hc₁G : (y⁻¹ * e : G) ∈ A := by
    have : (((k₀ * ⟨r, hr⟩ * k₀⁻¹)⁻¹ * ⟨e, he⟩ : ↥K) : G) = y⁻¹ * e := by
      simp [hy]
    rw [← this]; exact hc₁A
  have hcA : (e⁻¹ * y : G) ∈ A := by
    have h1 := A.inv_mem hc₁G
    simpa using h1
  set c : G := e⁻¹ * y with hc
  have hyec : y = e * c := by rw [hc]; group
  have he_inv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
  have hcc : c * c = 1 := h.mul_self hcA
  have hfix : e * c * e⁻¹ = c := by
    have h1 : e * c * (e * c) = 1 := by rw [← hyec]; exact hy2
    have h2 : e * c * e = c⁻¹ := by
      have : e * c * e * c = 1 := by simpa [mul_assoc] using h1
      exact eq_inv_of_mul_eq_one_left this
    have h3 : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    rw [he_inv, h2, h3]
  have hecA : e * c * e⁻¹ ∈ A := h.conj_mem he hcA
  have hact := hψ ⟨e, he⟩ ⟨c, hcA⟩ hecA
  have hψc : ψ ⟨c, hcA⟩ = n6Act (σe : Equiv.Perm (Fin 6)) (ψ ⟨c, hcA⟩) := by
    have : (⟨e * c * e⁻¹, hecA⟩ : ↥A) = ⟨c, hcA⟩ := Subtype.ext hfix
    have h1 := hact
    rw [this] at h1
    simpa [hqe, hσe] using h1
  obtain ⟨-, hexists⟩ := n6_invol _ σe.2 hσe1 hσe2
  obtain ⟨b, hb⟩ := hexists _ hψc.symm
  set b' : ↥A := ψ.symm b with hb'
  have hψb' : ψ b' = b := by simp [hb']
  have hact2 := hψ ⟨e, he⟩ b' (h.conj_mem he b'.2)
  have hcb : c = e * (b' : G) * e⁻¹ * (b' : G)⁻¹ := by
    have h1 : ψ ⟨c, hcA⟩ = ψ ⟨e * (b' : G) * e⁻¹, h.conj_mem he b'.2⟩ * (ψ b')⁻¹ := by
      rw [hact2, hψb', hb]
    have h2 : (⟨c, hcA⟩ : ↥A) =
        ⟨e * (b' : G) * e⁻¹, h.conj_mem he b'.2⟩ * b'⁻¹ := by
      apply ψ.injective
      rw [h1, map_mul, map_inv]
    exact congrArg Subtype.val h2
  refine ⟨k₀, k₀.2, (b' : G), b'.2, ?_⟩
  rw [← hy, hyec, hcb, he_inv]
  calc e * (e * (b' : G) * e * (b' : G)⁻¹) = (e * e) * (b' : G) * e * (b' : G)⁻¹ := by group
    _ = (b' : G) * e * (b' : G)⁻¹ := by rw [he2]; group

theorem card_conjSubgroup (A : Subgroup G) (t : G) : Nat.card (conjSubgroup A t) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj t⁻¹).injective

end S143

open S143 in
theorem lemma_14_3_21_three :
    ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
      Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
        Subgroup.centralizer (A : Set G) = A →
          ∀ r ∈ rOf T M ⊔ uOfL22 T M, orderOf r = 2 →
            ∃ y : G, ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 ∧ y * z * y⁻¹ = r := by
  intro G _ _ T M g A t hc c18 c19 _ r hr hr2
  obtain ⟨hr2', hr1⟩ := orderOf_eq_prime_iff.mp hr2
  have hrr : r * r = 1 := by rw [← pow_two]; exact hr2'
  obtain ⟨z₀, hz₀Z, hz₀1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc.h1281.omegaOneCenter_ne_bot
    exact ⟨z, z.2, fun h => hz (Subtype.ext h)⟩
  have hZV : quasithinOmegaOneCenter T ≤ VZ T M := le_conjClosure _ _
  have hVA : VZ T M ≤ A := c18.b.v_eq_inf ▸ inf_le_left
  have hz₀A : z₀ ∈ A := hVA (hZV hz₀Z)
  have hK := c19.b.block
  have hRUK : rOf T M ⊔ uOfL22 T M ≤ kOf T M A := c19.b.sylow_RU.1
  have hrK : r ∈ kOf T M A := hRUK hr
  by_cases hrA : r ∈ A
  · obtain ⟨k, -, hk⟩ := hK.exists_conj_of_ne_one hz₀A hrA hz₀1 hr1
    exact ⟨k, z₀, hz₀Z, hz₀1, hk⟩
  ·
    have hnle : ¬ conjSubgroup A t ≤ A := by
      intro hle
      have h1 : VZ T M = conjSubgroup A t := by
        rw [c18.b.v_eq_inf]; exact inf_eq_right.mpr hle
      have h2 := hc.hyp.rank_two
      rw [h1, card_conjSubgroup, c18.b.A_card] at h2
      omega
    obtain ⟨e, heAt, heA⟩ := Set.not_subset.mp hnle
    have ha₁ : t * e * t⁻¹ ∈ A := mem_conjSubgroup_iff.mp heAt
    have he2 : e * e = 1 := by
      have h1 := hK.mul_self ha₁
      calc e * e = t⁻¹ * ((t * e * t⁻¹) * (t * e * t⁻¹)) * t := by group
        _ = 1 := by rw [h1]; group
    have he1 : e ≠ 1 := fun h => heA (h ▸ A.one_mem)
    have heR : e ∈ rOf T M := by
      rw [c18.b.r_eq_AAt]; exact Subgroup.mem_sup_right heAt
    have heK : e ∈ kOf T M A := hRUK (Subgroup.mem_sup_left heR)
    obtain ⟨k, -, b, hbA, hkb⟩ := hK.exists_conj_involution hrK heK hrA heA hrr he2
    have ha₁1 : t * e * t⁻¹ ≠ 1 := fun h => he1 (by
      have : e = t⁻¹ * (t * e * t⁻¹) * t := by group
      rw [this, h]; group)
    obtain ⟨k₂, -, hk₂⟩ := hK.exists_conj_of_ne_one hz₀A ha₁ hz₀1 ha₁1
    refine ⟨k⁻¹ * b * t⁻¹ * k₂, z₀, hz₀Z, hz₀1, ?_⟩
    have e1 : r = k⁻¹ * (b * e * b⁻¹) * k := by rw [← hkb]; group
    have e2 : e = t⁻¹ * (k₂ * z₀ * k₂⁻¹) * t := by rw [hk₂]; group
    rw [e1, e2]
    group

end CFSG.Quasithin
