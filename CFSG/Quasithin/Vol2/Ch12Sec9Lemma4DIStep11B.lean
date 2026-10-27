module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep11A
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIStep10B

public section

namespace CFSG.Quasithin.H13.C1294

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Quasithin.H13

open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

section Env

variable {T L V V₁ V₂ K₁ : Subgroup G} {g : G} {D : HatModelU (u128 V V₁)}

@[expose] noncomputable def DIEnv.N0G (E : DIEnv T L V V₁ V₂ K₁ g D) : Subgroup G :=
  (E.sigma.ker).map (k0Sub K₁ D (D.π E.a)).subtype

theorem DIEnv.mem_N0G (E : DIEnv T L V V₁ V₂ K₁ g D) {x : G} :
    x ∈ E.N0G ↔ ∃ hx : x ∈ k0Sub K₁ D (D.π E.a), E.sigma ⟨x, hx⟩ = 1 := by
  constructor
  · intro h
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 h
    have hyx' : (y : G) = x := hyx
    have hxK : x ∈ k0Sub K₁ D (D.π E.a) := hyx' ▸ y.2
    refine ⟨hxK, ?_⟩
    have : (⟨x, hxK⟩ : ↥(k0Sub K₁ D (D.π E.a))) = y := Subtype.ext hyx'.symm
    rw [this]
    exact MonoidHom.mem_ker.1 hy
  · rintro ⟨hx, h⟩
    exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, MonoidHom.mem_ker.2 h, rfl⟩

theorem DIEnv.N0G_le_K0 (E : DIEnv T L V V₁ V₂ K₁ g D) : E.N0G ≤ k0Sub K₁ D (D.π E.a) := by
  intro x hx
  exact (E.mem_N0G.1 hx).choose

theorem DIEnv.N0G_normal (E : DIEnv T L V V₁ V₂ K₁ g D) {g' : G}
    (hg : g' ∈ k0Sub K₁ D (D.π E.a)) {n : G} (hn : n ∈ E.N0G) :
    g' * n * g'⁻¹ ∈ E.N0G := by
  obtain ⟨hnK, hσ⟩ := E.mem_N0G.1 hn
  rw [E.mem_N0G]
  have hconj : g' * n * g'⁻¹ ∈ k0Sub K₁ D (D.π E.a) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hnK) (Subgroup.inv_mem _ hg)
  refine ⟨hconj, ?_⟩
  have e : (⟨g' * n * g'⁻¹, hconj⟩ : ↥(k0Sub K₁ D (D.π E.a))) =
      ⟨g', hg⟩ * ⟨n, hnK⟩ * ⟨g', hg⟩⁻¹ := Subtype.ext (by simp [mul_assoc])
  rw [e, map_mul, map_mul, map_inv, hσ, mul_one, mul_inv_cancel]


theorem DIEnv.N0_ccF_mem (E : DIEnv T L V V₁ V₂ K₁ g D) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h1289 : Lemma12_8_9W) (h12810 : Lemma12_8_10)
    (h12813 : Lemma12_8_13) (h12813f : Lemma12_8_13_five) (F2 : FactF2) (F3 : FactF3)
    (hpt : kmapOf (D.img K₁) E.kap (stabS E.S) = stabS E.fp)
    (hK₁C : quasithinIsCComponent K₁ (Subgroup.normalizer (V₁ : Set G)))
    (hK4 : Nonempty (↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)))
    (hG5 : G112Concl5 D.B (D.img (Subgroup.normalizer (V₁ : Set G))))
    (hK₁N : ∀ h ∈ Subgroup.normalizer (V₁ : Set G), ∀ k ∈ K₁, h * k * h⁻¹ ∈ K₁)
    {k : G} (hk : k ∈ E.N0G) : ccF E.a k ∈ (E.I ⊓ wcSub T L V V₁) ⊔ V₁ := by
  classical
  have hzc : ∀ x ∈ zU128 V V₁, ∀ y ∈ zU128 V V₁, x * y = y * x := fun x hx y hy =>
    (mem_centerOf_iff'.1 hy).2 x (zU_le_u128 hx)
  have hV1Z : V₁ ≤ zU128 V V₁ := V₁_le_zU h1222 h12213 E.hs
  have hIZ := E.hIZ
  have hIV1Z : E.I ⊔ V₁ ≤ zU128 V V₁ := sup_le hIZ hV1Z
  have hcIV1 : ∀ x ∈ E.I ⊔ V₁, ∀ y ∈ E.I ⊔ V₁, x * y = y * x := fun x hx y hy =>
    hzc x (hIV1Z hx) y (hIV1Z hy)
  have hdec : ∀ z ∈ E.I ⊔ V₁, ∃ i ∈ E.I, ∃ v ∈ V₁, z = i * v := fun z hz =>
    mem_sup_decomp (fun i hi v hv => hzc i (hIZ hi) v (hV1Z hv)) z hz
  have hKZ : ∀ k' ∈ E.N0G, ∀ z ∈ E.I ⊔ V₁, k' * z * k'⁻¹ ∈ E.I ⊔ V₁ := by
    intro k' hk' z hz
    obtain ⟨hk'K0⟩ : Nonempty (k' ∈ k0Sub K₁ D (D.π E.a)) := ⟨E.N0G_le_K0 hk'⟩
    obtain ⟨hk'K1, hk'N, hρ⟩ := mem_k0Sub.1 hk'K0
    obtain ⟨i, hi, v, hv, rfl⟩ := hdec z hz
    have hiI : k' * i * k'⁻¹ ∈ E.I := (Subgroup.mem_normalizer_iff.1 (E.hKI hk'K1) i).1 hi
    have hvv : k' * v * k'⁻¹ = v := conj_fix_V1 (card_V₁ E.hs) (E.hK₁H hk'K1) hv
    have e : k' * (i * v) * k'⁻¹ = (k' * i * k'⁻¹) * (k' * v * k'⁻¹) := by group
    rw [e, hvv]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hiI) (Subgroup.mem_sup_right hv)
  have htriv : ∀ k' ∈ E.N0G, ∀ z ∈ E.I ⊔ V₁,
      k' * z * k'⁻¹ * z⁻¹ ∈ (E.I ⊓ wcSub T L V V₁) ⊔ V₁ := by
    intro k' hk' z hz
    obtain ⟨hK0, hσ⟩ := E.mem_N0G.1 hk'
    obtain ⟨hk'K1, hk'N, hρ⟩ := mem_k0Sub.1 hK0
    obtain ⟨i, hi, v, hv, rfl⟩ := hdec z hz
    have hvv : k' * v * k'⁻¹ = v := conj_fix_V1 (card_V₁ E.hs) (E.hK₁H hk'K1) hv
    have hd := E.sigma_one_mem h1222 h12213 h1289 h12810 h12813 F2 F3 hpt hK0 hσ hi
    have e : k' * (i * v) * k'⁻¹ * (i * v)⁻¹ = k' * i * k'⁻¹ * i⁻¹ := by
      calc k' * (i * v) * k'⁻¹ * (i * v)⁻¹ = (k' * i * k'⁻¹) * (k' * v * k'⁻¹) * v⁻¹ * i⁻¹ := by
            group
        _ = (k' * i * k'⁻¹) * v * v⁻¹ * i⁻¹ := by rw [hvv]
        _ = k' * i * k'⁻¹ * i⁻¹ := by group
    rw [e]
    exact Subgroup.mem_sup_left hd
  haveI : ((E.I ⊓ wcSub T L V V₁ ⊔ V₁).subgroupOf (E.I ⊔ V₁)).Normal :=
    subgroupOf_normal_of_comm hcIV1
  have hcZ : ∀ k' ∈ E.N0G, ccF E.a k' ∈ E.I ⊔ V₁ := fun k' hk' =>
    E.ccF_mem_IV1 h1222 h12213 h1289 h12810 h12813 h12813f F2 F3 hpt hK₁C hK4 hG5 hK₁N
      (E.N0G_le_K0 hk')
  obtain ⟨ψ, hψ⟩ := hom_quot (K0 := E.N0G) hcIV1 hKZ (ccF E.a) (ccF_one E.a) hcZ
    (fun k' _ l _ => ccF_mul E.a k' l) htriv
  have hT2 : IsPGroup (2 : ℕ) (T ⊓ E.N0G : Subgroup G) := E.hcx.hyp.hyp.sylow.1.to_inf_left
  have hS2 : IsPGroup (2 : ℕ) ((T ⊓ E.N0G : Subgroup G).subgroupOf E.N0G) := hT2.comap_subtype
  have hSyl : ¬ 2 ∣ ((T ⊓ E.N0G : Subgroup G).subgroupOf E.N0G).index := by
    have hsupN : ∀ g' ∈ E.N0G ⊔ (T ⊓ k0Sub K₁ D (D.π E.a)), ∀ k' ∈ E.N0G,
        g' * k' * g'⁻¹ ∈ E.N0G := by
      intro g' hg' k' hk'
      have hg'K0 : g' ∈ k0Sub K₁ D (D.π E.a) := sup_le (E.N0G_le_K0) inf_le_right hg'
      exact E.N0G_normal hg'K0 hk'
    have hrel := relIndex_sup_eq_of_normalizes hsupN
    have hmul := Subgroup.relIndex_mul_relIndex (T ⊓ k0Sub K₁ D (D.π E.a))
      (E.N0G ⊔ (T ⊓ k0Sub K₁ D (D.π E.a))) (k0Sub K₁ D (D.π E.a)) le_sup_right
      (sup_le (E.N0G_le_K0) inf_le_right)
    have hset : (T ⊓ k0Sub K₁ D (D.π E.a)) ⊓ E.N0G = T ⊓ E.N0G := by
      rw [inf_assoc, inf_eq_right.2 E.N0G_le_K0]
    have hPN : (T ⊓ k0Sub K₁ D (D.π E.a)).relIndex E.N0G = (T ⊓ E.N0G).relIndex E.N0G := by
      rw [← hset]
      exact (Subgroup.inf_relIndex_right _ _).symm
    have hodd := T_inf_K0_odd E h1222 h12213 hK₁N
    intro h2
    apply hodd
    have hchain : (T ⊓ E.N0G).relIndex E.N0G ∣
        (T ⊓ k0Sub K₁ D (D.π E.a)).relIndex (k0Sub K₁ D (D.π E.a)) := by
      rw [← hPN, ← hrel]
      exact ⟨_, hmul.symm⟩
    exact dvd_trans h2 hchain
  have hsq : ∀ x : ↥E.N0G, ψ x ^ 2 = 1 := by
    rintro ⟨y, hy⟩
    rw [hψ y hy, ← QuotientGroup.mk_pow]
    have hu : (⟨ccF E.a y, hcZ y hy⟩ : ↥(E.I ⊔ V₁)) ^ 2 = 1 :=
      Subtype.ext (by simpa using ccF_sq E (E.N0G_le_K0 hy))
    rw [hu]
    rfl
  have hSA : (T ⊓ E.N0G : Subgroup G).subgroupOf E.N0G ≤ ψ.ker := by
    intro x hx
    obtain ⟨y, hy⟩ := x
    have hyT : y ∈ T := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hx)).1
    rw [MonoidHom.mem_ker, hψ y hy, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_right (ccF_T_mem_V1 E hyT (mem_k0Sub.1 (E.N0G_le_K0 hy)).1)
  have hodd : ∀ x : ↥E.N0G, Odd (orderOf x) → x ∈ ψ.ker := fun x hx => by
    rw [MonoidHom.mem_ker]
    exact hom_odd_trivial ψ hsq x hx
  have htop := sylow_odd_normal ψ.ker ((T ⊓ E.N0G : Subgroup G).subgroupOf E.N0G) hS2 hSyl hSA hodd
  have hkA : (⟨k, hk⟩ : ↥E.N0G) ∈ ψ.ker := by
    rw [htop]
    exact Subgroup.mem_top _
  rw [MonoidHom.mem_ker, hψ k hk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hkA
  exact hkA

end Env

end CFSG.Quasithin.H13.C1294
