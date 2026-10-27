module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLaMainAux
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKLinPerf

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open hiding StatedSL
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem laMain {K Q V : Subgroup G} {F : Type} [Field F] [Fintype F]
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hco : CoordData K Q F α β) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥K) (hF : ∃ m : ℕ, 2 ≤ m ∧ Fintype.card F = 2 ^ m)
    (hV : VStruct K Q V F α) {t : G} (ht : t ∈ K)
    (htV : ∀ q ∈ V, t * q * t⁻¹ ∈ V) (ht2 : ∀ q ∈ V, t * t * q = q * (t * t))
    (S : Set G) (hS : ∀ a ∈ S, ∃ q ∈ V, a = ⁅t, q⁆) (hSne : ∃ a ∈ S, a ≠ 1) :
    (∃ ρ : ↥(perfectCore (K ⊓ Subgroup.centralizer ((Subgroup.closure S : Subgroup G) : Set G))) →*
        ↥(StatedSL 2 F), Function.Surjective ρ ∧ IsPGroup 2 ρ.ker) ∧
      ⁅V, perfectCore (K ⊓ Subgroup.centralizer ((Subgroup.closure S : Subgroup G) : Set G))⁆ =
        Q := by
  obtain ⟨m, hm2, hmF⟩ := hF
  have h4 : 4 ≤ Fintype.card F := by
    rw [hmF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  have hchar : (2 : F) = 0 := by
    have hc : ringChar F = 2 := FiniteField.even_card_iff_char_two.mpr
      (by rw [hmF]; exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 (by omega)))
    have h := CharP.cast_eq_zero F (ringChar F)
    rw [hc] at h
    exact_mod_cast h
  obtain ⟨g₀, hg₀K, -, hg₀V⟩ := hV.exists_g₀
  obtain ⟨ℓ, hVℓ⟩ : ∃ ℓ : Submodule F (Fin 3 → F),
      ∀ q : ↥Q, (q : G) ∈ V ↔ ∀ i : Fin 2, coord β q i ∈ ℓ :=
    ⟨_, mem_V_iff_laMain hco hg₀K hg₀V⟩
  have hℓ2 : Module.finrank F ℓ = 2 :=
    finrank_fixSpace_laMain hco hV.VQ hVℓ (by omega) hV.card
  obtain ⟨T, hT⟩ : ∃ T : Matrix (Fin 3) (Fin 3) F, matOf (α ⟨t, ht⟩) = T := ⟨_, rfl⟩
  have hTℓ : ∀ x ∈ ℓ, T *ᵥ x ∈ ℓ := by
    intro x hx
    obtain ⟨q, hq0, hq1⟩ := exists_coord_laMain hco x 0
    have hqV : (q : G) ∈ V := (hVℓ q).mpr (Fin.forall_fin_two.mpr
      ⟨by rw [hq0]; exact hx, by rw [hq1]; exact ℓ.zero_mem⟩)
    have hmem : t * (q : G) * t⁻¹ ∈ Q := memQ_conj_laMain hco ht q.2
    have h1 := (hVℓ ⟨t * (q : G) * t⁻¹, hmem⟩).mp (htV _ hqV) 0
    have h2 := coord_conj_laMain hco ht (u := q) (v := ⟨t * (q : G) * t⁻¹, hmem⟩) rfl 0
    rw [hT, hq0] at h2
    rw [← h2]
    exact h1
  have hMs : matOf (α ⟨t * t, K.mul_mem ht ht⟩) = T * T := by
    rw [← hT]
    have e : (⟨t * t, K.mul_mem ht ht⟩ : ↥K) = ⟨t, ht⟩ * ⟨t, ht⟩ := rfl
    rw [e, map_mul]
    exact matOf_mul_laMain _ _
  have hT2 : ∀ x ∈ ℓ, T *ᵥ (T *ᵥ x) = x := by
    intro x hx
    obtain ⟨q, hq0, hq1⟩ := exists_coord_laMain hco x 0
    have hqV : (q : G) ∈ V := (hVℓ q).mpr (Fin.forall_fin_two.mpr
      ⟨by rw [hq0]; exact hx, by rw [hq1]; exact ℓ.zero_mem⟩)
    have hconj : (t * t) * (q : G) * (t * t)⁻¹ = (q : G) := by
      rw [mul_inv_eq_iff_eq_mul]
      exact ht2 _ hqV
    have hfix := (conj_fix_iff_laMain hco (K.mul_mem ht ht) q).mp hconj 0
    rw [hMs, hq0, ← Matrix.mulVec_mulVec] at hfix
    exact hfix
  obtain ⟨a₀, ha₀S, ha₀ne⟩ := hSne
  obtain ⟨q₀, hq₀V, rfl⟩ := hS a₀ ha₀S
  have hq₀Q : q₀ ∈ Q := hV.VQ hq₀V
  obtain ⟨aQ₀, haQ₀⟩ : ∃ aQ₀ : ↥Q, (aQ₀ : G) = ⁅t, q₀⁆ :=
    ⟨⟨⁅t, q₀⁆, comm_mem_Q_laMain hco ht hq₀Q⟩, rfl⟩
  have haQ₀ne : aQ₀ ≠ 1 := fun h => ha₀ne (by rw [← haQ₀, h, Subgroup.coe_one])
  obtain ⟨i₀, hi₀⟩ := exists_coord_ne_zero_laMain hco haQ₀ne
  have hx₀ : coord β ⟨q₀, hq₀Q⟩ i₀ ∈ ℓ := (hVℓ ⟨q₀, hq₀Q⟩).mp hq₀V i₀
  have hcoord₀ : coord β aQ₀ i₀ = (T - 1) *ᵥ coord β ⟨q₀, hq₀Q⟩ i₀ := by
    have e : aQ₀ = ⟨⁅t, q₀⁆, comm_mem_Q_laMain hco ht hq₀Q⟩ := Subtype.ext haQ₀
    have h := coord_comm_laMain hco ht ⟨q₀, hq₀Q⟩ (comm_mem_Q_laMain hco ht hq₀Q) i₀
    rw [hT] at h
    rw [e]
    exact h
  obtain ⟨w₀, hw₀, hw0⟩ := exists_w0_laMain T ℓ hℓ2 hchar hTℓ hT2
    ⟨_, hx₀, by rw [← hcoord₀]; exact hi₀⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c : F, coord β aQ₀ i₀ = c • w₀ := by
    obtain ⟨c, hc⟩ := hw0 _ hx₀
    exact ⟨c, hcoord₀.trans hc⟩
  have hc₀ne : c₀ ≠ 0 := by
    rintro rfl
    apply hi₀
    rw [hc₀, zero_smul]
  have hSform : ∀ a ∈ S, ∃ aQ : ↥Q, (aQ : G) = a ∧
      ∀ i : Fin 2, ∃ c : F, coord β aQ i = c • w₀ := by
    intro a ha
    obtain ⟨q, hqV, rfl⟩ := hS a ha
    have hqQ : q ∈ Q := hV.VQ hqV
    refine ⟨⟨⁅t, q⁆, comm_mem_Q_laMain hco ht hqQ⟩, rfl, fun i => ?_⟩
    obtain ⟨c, hc⟩ := hw0 (coord β ⟨q, hqQ⟩ i) ((hVℓ ⟨q, hqQ⟩).mp hqV i)
    exact ⟨c, (coord_comm_laMain hco ht ⟨q, hqQ⟩ (comm_mem_Q_laMain hco ht hqQ) i).trans
      (by rw [hT]; exact hc)⟩
  have hE : ∀ k : ↥K, (k : G) ∈ Subgroup.centralizer S ↔ (matOf (α k)).mulVec w₀ = w₀ := by
    intro k
    rw [Subgroup.mem_centralizer_iff]
    constructor
    · intro hk
      have hfix : (k : G) * (aQ₀ : G) * (k : G)⁻¹ = (aQ₀ : G) := by
        rw [haQ₀, mul_inv_eq_iff_eq_mul]
        exact (hk _ ha₀S).symm
      have hfix' := (conj_fix_iff_laMain hco k.2 aQ₀).mp hfix i₀
      rw [hc₀, Matrix.mulVec_smul] at hfix'
      exact smul_right_injective _ hc₀ne hfix'
    · intro hk' a ha
      obtain ⟨aQ, haQ, hcq⟩ := hSform a ha
      have hfixQ : ∀ i : Fin 2, (matOf (α k)).mulVec (coord β aQ i) = coord β aQ i := by
        intro i
        obtain ⟨c, hc⟩ := hcq i
        rw [hc, Matrix.mulVec_smul, hk']
      have hfix := (conj_fix_iff_laMain hco k.2 aQ).mpr hfixQ
      rw [haQ] at hfix
      exact (mul_inv_eq_iff_eq_mul.mp hfix).symm
  obtain ⟨S₀, hS₀def⟩ : ∃ S₀ : Subgroup ↥(StatedSL 3 F),
      S₀ = (stabVec w₀).map (specialLinearGroupEquivStatedSL 3 F :
        SpecialLinearGroup (Fin 3) F →* ↥(StatedSL 3 F)) := ⟨_, rfl⟩
  have hS₀mem : ∀ s : ↥(StatedSL 3 F), s ∈ S₀ ↔ (matOf s).mulVec w₀ = w₀ := fun s => by
    rw [hS₀def]
    exact mem_stabMap_iff_laMain w₀ s
  have hS₀perf : ⁅S₀, S₀⁆ = S₀ := by
    rw [hS₀def, ← Subgroup.map_commutator, stabVec_perfect h4 hw₀]
  obtain ⟨H, hHdef⟩ : ∃ H : Subgroup G,
      H = K ⊓ Subgroup.centralizer ((Subgroup.closure S : Subgroup G) : Set G) := ⟨_, rfl⟩
  rw [← hHdef]
  have hHK : H ≤ K := by
    rw [hHdef]
    exact inf_le_left
  have hHmem : ∀ k : ↥K, (k : G) ∈ H ↔ α k ∈ S₀ := fun k => by
    rw [hHdef, Subgroup.mem_inf, Subgroup.centralizer_closure, hS₀mem, ← hE k]
    exact ⟨fun h => h.2, fun h => ⟨k.2, h⟩⟩
  have hPK : perfectCore H ≤ K := (perfectCore_le H).trans hHK
  obtain ⟨himg₁, himg₂⟩ := perfect_image_laMain hα hHK hS₀perf hHmem
  obtain ⟨φ, hφ⟩ : ∃ φ : ↥(perfectCore H) →* ↥(StatedSL 3 F),
      ∀ x : ↥(perfectCore H), φ x = α ⟨x.1, hPK x.2⟩ :=
    ⟨α.comp (Subgroup.inclusion hPK), fun x => rfl⟩
  have hφmem : ∀ x : ↥(perfectCore H), (matOf (φ x)).mulVec w₀ = w₀ := fun x => by
    obtain ⟨_, hmem⟩ := himg₁ x.1 x.2
    rw [hφ x]
    exact (hS₀mem _).mp hmem
  have hran : ∀ s : ↥(StatedSL 3 F), (matOf s).mulVec w₀ = w₀ →
      ∃ x : ↥(perfectCore H), φ x = s := by
    intro s hs
    obtain ⟨b, hbP, hbK, hbs⟩ := himg₂ s ((hS₀mem s).mpr hs)
    exact ⟨⟨b, hbP⟩, by rw [hφ]; exact hbs⟩
  have hsq : ∀ x : ↥(perfectCore H), φ x * φ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    have hxK : (x : G) ∈ K := hPK x.2
    have hyy : (⟨(x : G), hxK⟩ : ↥K) * ⟨(x : G), hxK⟩ ∈ α.ker := by
      rw [MonoidHom.mem_ker, map_mul]
      rw [hφ] at hx
      exact hx
    rw [hker] at hyy
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, hyy⟩
    have hk2 : ((x : G) * x) ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val hk
      simpa using h
    refine ⟨k + 1, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, show (2 : ℕ) ^ (k + 1) = 2 * 2 ^ k from by ring,
      pow_mul, pow_two]
    exact hk2
  obtain ⟨ρ, hρsurj, hρker⟩ := exists_rho_laMain hchar hw₀ φ hφmem hran hsq
  refine ⟨⟨ρ, hρsurj, hρker⟩, ?_⟩
  have hP : ∀ g ∈ stabVec w₀, ∃ b ∈ perfectCore H, ∃ hb : b ∈ K,
      matOf (α ⟨b, hb⟩) = (g : Matrix (Fin 3) (Fin 3) F) := by
    intro g hg
    have hgS : specialLinearGroupEquivStatedSL 3 F g ∈ S₀ := by
      rw [hS₀mem, matOf_equiv_laMain]
      exact mem_stabVec.mp hg
    obtain ⟨b, hbP, hbK, hbs⟩ := himg₂ _ hgS
    exact ⟨b, hbP, hbK, by rw [hbs, matOf_equiv_laMain]⟩
  exact commutator_eq_laMain hco hV.VQ hPK hℓ2 hVℓ hw₀ h4 hP

end CFSG.Quasithin.H13.Ch4.CentK
