module

public import CFSG.Milestones.ASVolI.A3L3.Glue
public import CFSG.Milestones.ASVolI.A3L3.Sylow

public section

namespace CFSG.ASVolI

open Matrix CFSG.RankThree.SubgroupLists CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3
open scoped Pointwise

@[expose] noncomputable def burnsideA315y_equivMap {G Y : Type} [Group G] [Group Y] (f : G →* Y)
    (H : Subgroup G) (hker : ∀ h ∈ H, f h = 1 → h = 1) : ↥H ≃* ↥(H.map f) :=
  (MonoidHom.ofInjective (f := f.comp H.subtype) (by
    rw [injective_iff_map_eq_one]
    intro h hh
    exact Subtype.ext (hker h h.2 hh))).trans
    (MulEquiv.subgroupCongr (by rw [← MonoidHom.map_range, Subgroup.range_subtype]))

theorem burnsideA315y_card_map_of_ker {G Y : Type} [Group G] [Group Y] (f : G →* Y)
    (H : Subgroup G) (hker : ∀ h ∈ H, f h = 1 → h = 1) : Nat.card ↥(H.map f) = Nat.card ↥H :=
  (Nat.card_congr (burnsideA315y_equivMap f H hker).toEquiv).symm

theorem burnsideA315y_relIndex_map_dvd {G Y : Type} [Group G] [Group Y] (f : G →* Y)
    {H K : Subgroup G} (hHK : H ≤ K) : (H.map f).relIndex (K.map f) ∣ H.relIndex K := by
  let fK : ↥K →* ↥(K.map f) :=
    (f.comp K.subtype).codRestrict (K.map f) (fun k => ⟨k, k.2, rfl⟩)
  have hfK : Function.Surjective fK := by
    rintro ⟨_, k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩
  have h1 : (H.map f).subgroupOf (K.map f) = (H.subgroupOf K).map fK := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hHK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    · rintro ⟨⟨x, hxK⟩, hx, hxy⟩
      exact ⟨x, Subgroup.mem_subgroupOf.mp hx, congrArg Subtype.val hxy⟩
  show ((H.map f).subgroupOf (K.map f)).index ∣ (H.subgroupOf K).index
  rw [h1]
  exact Subgroup.index_map_dvd _ hfK

theorem burnsideA315y_relIndex_inf_odd {Γ : Type} [Group Γ] {S C N : Subgroup Γ} (hSC : S ≤ C)
    (hNC : N ≤ C) (hCN : C ≤ Subgroup.normalizer (N : Set Γ)) (hS : ¬ 2 ∣ S.relIndex C) :
    ¬ 2 ∣ (S ⊓ N).relIndex N := by
  have h1 : S.relIndex (N ⊔ S) = S.relIndex N := burnsideA315x_relIndex_sup (hSC.trans hCN)
  have h2 : S.relIndex (N ⊔ S) ∣ S.relIndex C :=
    Dvd.intro _ (Subgroup.relIndex_mul_relIndex S (N ⊔ S) C le_sup_right (sup_le hNC hSC))
  have h3 : (S ⊓ N).relIndex N = S.relIndex N := Subgroup.inf_relIndex_right S N
  intro h
  apply hS
  rw [h3, ← h1] at h
  exact h.trans h2

theorem burnsideA315y_card_eq_two_pow {Γ : Type} [Group Γ] [Finite Γ] {Q N : Subgroup Γ}
    (hQN : Q ≤ N) (hQ : IsPGroup 2 ↥Q) (hodd : ¬ 2 ∣ Q.relIndex N) :
    Nat.card ↥Q = 2 ^ (Nat.card ↥N).factorization 2 := by
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have h1 : Q.relIndex N * Nat.card ↥(Q ⊓ N) = Nat.card ↥N := Subgroup.relIndex_mul_card Q N
  rw [inf_eq_left.mpr hQN, hk] at h1
  have hm0 : Q.relIndex N ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  rw [hk, ← h1, Nat.factorization_mul hm0 (pow_ne_zero _ two_ne_zero), Finsupp.add_apply,
    Nat.factorization_eq_zero_of_not_dvd hodd, Nat.Prime.factorization_pow Nat.prime_two,
    Finsupp.single_eq_same, zero_add]

theorem burnsideA315y_card_SL2 (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) =
      Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod p)) := by
  have hp : p.Prime := Fact.out
  have h1 := Matrix.card_SL_mul_card_units (n := Fin 2) (R := ZMod p)
  rw [Matrix.card_GL_field, Nat.card_units, Fin.prod_univ_two, Nat.card_zmod, ZMod.card] at h1
  rw [CFSG.GorensteinWalter.pgl2_card_formula, Nat.card_zmod]
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  apply Nat.eq_of_mul_eq_mul_right hp1
  rw [h1]
  simp only [Fin.val_zero, pow_zero, Fin.val_one, pow_one]
  have h2 : p ^ 2 - p = p * (p - 1) := by
    rw [Nat.mul_sub, mul_one, sq]
  rw [h2]
  ring

namespace burnsideA315y_Model

variable {F : Type} [Field F] {X : Type} [Group X] (M : burnsideA315y_Model F X)

theorem C₁_le_Γ₁ : M.C₁ ≤ M.Γ₁ := fun _ hg => hg.1

theorem C₁_comm {g : ↥M.Γ} (hg : g ∈ M.C₁) :
    (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g := by
  have h1 : ((g * M.zh : ↥M.Γ) : GL (Fin 3) F) = ((M.zh * g : ↥M.Γ) : GL (Fin 3) F) :=
    congrArg Subtype.val hg.2
  rwa [Subgroup.coe_mul, Subgroup.coe_mul, M.zh_val] at h1

theorem C₁_block {g : ↥M.Γ} (hg : g ∈ M.C₁) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 1 2 = 0 ∧
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 0 = 0 ∧
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := by
  have hm : ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) * diagonal ![-1, -1, 1] =
      diagonal ![-1, -1, 1] * ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
    rw [← coe_negDiag3, ← Units.val_mul, M.C₁_comm hg, Units.val_mul]
  exact block_eq_zero_of_commute_negDiag M.two_ne hm

theorem C₁_22_ne {g : ↥M.Γ} (hg : g ∈ M.C₁) :
    ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 ≠ 0 := by
  intro h0
  obtain ⟨h02, h12, h20, h21⟩ := M.C₁_block hg
  have hd := hg.1
  rw [Matrix.det_fin_three, h02, h12, h20, h21, h0] at hd
  simp at hd

@[expose] noncomputable def e22 : ↥M.C₁ →* Fˣ where
  toFun g := Units.mk0 ((((g : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2)
    (M.C₁_22_ne g.2)
  map_one' := by
    apply Units.ext
    simp
  map_mul' a b := by
    apply Units.ext
    obtain ⟨-, -, a20, a21⟩ := M.C₁_block a.2
    obtain ⟨b02, b12, -, -⟩ := M.C₁_block b.2
    simp only [Subgroup.coe_mul, Units.val_mul, Units.val_mk0, Matrix.mul_apply, Fin.sum_univ_three,
      a20, a21, b02, b12, zero_mul, mul_zero, zero_add]

theorem e22_apply (g : ↥M.C₁) :
    ((M.e22 g : Fˣ) : F) = (((g : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 :=
  rfl

theorem K₀_le_C₁ : M.K₀ ≤ M.C₁ := by
  intro k hk
  refine ⟨hk.1, ?_⟩
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, M.zh_val]
  exact M.K₀_comm hk

theorem ker_e22 : M.e22.ker = M.K₀.subgroupOf M.C₁ := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have h22 : (((g : ↥M.Γ) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
      rw [← M.e22_apply, hg, Units.val_one]
    exact M.mem_K₀_of (M.C₁_comm g.2) h22 g.2.1
  · intro hg
    apply Units.ext
    rw [M.e22_apply, Units.val_one]
    exact hg.2.2.2.2.2

theorem card_C₁ [Finite F] : Nat.card ↥M.C₁ = Nat.card ↥M.K₀ * Nat.card ↥M.e22.range := by
  have h1 := Subgroup.card_mul_index M.e22.ker
  rw [Subgroup.index_ker, M.ker_e22] at h1
  have h2 : Nat.card ↥(M.K₀.subgroupOf M.C₁) = Nat.card ↥M.K₀ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe M.K₀_le_C₁).toEquiv
  rw [h2] at h1
  exact h1.symm

theorem c_K₀_ker {k : ↥M.Γ} (hk : k ∈ M.K₀) (h1 : M.c k = 1) : k = 1 := by
  obtain ⟨μ, hμ⟩ := M.exists_scalar_of_c_eq_one h1
  have h22 : ((k : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := hk.2.2.2.2.2
  rw [hμ] at h22
  have hμ1 : μ = 1 := Units.ext (by simpa [Matrix.GeneralLinearGroup.coe_scalar] using h22)
  apply Subtype.ext
  rw [hμ, hμ1, map_one, Subgroup.coe_one]

@[expose] noncomputable def K₀EquivK : ↥M.K₀ ≃* ↥M.K :=
  burnsideA315y_equivMap M.c M.K₀ (fun _ hk h1 => M.c_K₀_ker hk h1)

theorem card_K : Nat.card ↥M.K = Nat.card ↥M.K₀ :=
  burnsideA315y_card_map_of_ker M.c M.K₀ (fun _ hk h1 => M.c_K₀_ker hk h1)

theorem K_le_L : M.K ≤ M.L := Subgroup.map_mono fun _ hk => hk.1

theorem relIndex_L_dvd : M.L.relIndex M.c.range ∣ M.Γ₁.index := by
  have h := burnsideA315y_relIndex_map_dvd M.c (le_top : M.Γ₁ ≤ ⊤)
  rw [Subgroup.relIndex_top_right, ← MonoidHom.range_eq_map] at h
  exact h

theorem conj_mem_K₀ {g k : ↥M.Γ} (hgz : (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g)
    (hk : k ∈ M.K₀) : g * k * g⁻¹ ∈ M.K₀ := by
  have hkz := M.K₀_comm hk
  refine M.mem_K₀_of ?_ ?_ ?_
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Commute.mul_left (Commute.mul_left hgz hkz) (Commute.inv_left hgz)
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [burnsideA315y_conj_22' M.two_ne hgz hkz]
    exact hk.2.2.2.2.2
  · rw [M.det_conj]
    exact hk.1

theorem C₁_le_normalizer_K₀ : M.C₁ ≤ Subgroup.normalizer (M.K₀ : Set ↥M.Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro k
  have hgz := M.C₁_comm hg
  have hgz' : ((g⁻¹ : ↥M.Γ) : GL (Fin 3) F) * negDiag3 F = negDiag3 F * (g⁻¹ : ↥M.Γ) := by
    rw [Subgroup.coe_inv]
    exact Commute.inv_left hgz
  constructor
  · exact M.conj_mem_K₀ hgz
  · intro h
    have := M.conj_mem_K₀ hgz' h
    simpa [mul_assoc] using this

theorem C₁_le_normalizer_D₀ :
    M.C₁ ≤ Subgroup.normalizer ((M.D₀ ⊓ M.C₁ : Subgroup ↥M.Γ) : Set ↥M.Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro d
  have hgz := M.C₁_comm hg
  constructor
  · intro hd
    have h1 : g * d * g⁻¹ = d := by rw [← M.D₀_comm hd.1 hgz, mul_inv_cancel_right]
    rw [h1]
    exact hd
  · intro hd
    have h1 : g * d * g⁻¹ * g = g * (g * d * g⁻¹) := M.D₀_comm hd.1 hgz
    have h2 : d = g * d * g⁻¹ := by
      have h3 : g * d = g * (g * d * g⁻¹) := by rw [← h1]; group
      exact mul_left_cancel h3
    rw [h2]
    exact hd

theorem S₀_pow {s : ↥M.Γ} (hs : s ∈ M.S₀) : ∃ n : ℕ, s ^ 2 ^ n = 1 := by
  obtain ⟨n, hn⟩ := M.S₀_two ⟨s, hs⟩
  exact ⟨n, congrArg Subtype.val hn⟩

theorem c_S₀_ker {s : ↥M.Γ} (hs : s ∈ M.S₀) (h1 : M.c s = 1) : s = 1 := by
  obtain ⟨n, hn⟩ := M.S₀_pow hs
  exact M.lift_unique (Nat.Coprime.pow_left n (by norm_num)) (M.S₀_det s hs) (by simp) hn
    (one_pow _) (by rw [h1, map_one])

theorem S_inf_K : M.S ⊓ M.K = (M.S₀ ⊓ M.K₀).map M.c := by
  apply le_antisymm
  · rintro x ⟨⟨s, hs, rfl⟩, ⟨k, hk, hks⟩⟩
    obtain ⟨n, hn⟩ := M.S₀_pow hs
    have hkn : k ^ 2 ^ n = 1 := by
      apply M.c_K₀_ker (M.K₀.pow_mem hk _)
      rw [map_pow, hks, ← map_pow, hn, map_one]
    have hsk : s = k :=
      M.lift_unique (Nat.Coprime.pow_left n (by norm_num)) (M.S₀_det s hs) hk.1 hn hkn hks.symm
    exact ⟨s, ⟨hs, hsk ▸ hk⟩, rfl⟩
  · rintro _ ⟨s, ⟨hs, hk⟩, rfl⟩
    exact ⟨⟨s, hs, rfl⟩, ⟨s, hk, rfl⟩⟩

theorem scalar_mem_D₀ {σ : ↥M.Γ} {μ : Fˣ}
    (hσ : (σ : GL (Fin 3) F) = Matrix.GeneralLinearGroup.scalar (Fin 3) μ) : σ ∈ M.D₀ := by
  show σ ∈ Subgroup.centralizer ({M.zh, M.Da, M.Db} : Set ↥M.Γ)
  rw [Subgroup.mem_centralizer_iff]
  intro h _
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hσ]
  exact (burnsideA315y_scalar_comm μ _).symm

theorem S_inf_centralizer :
    M.S ⊓ Subgroup.centralizer (M.K : Set X) = (M.S₀ ⊓ (M.D₀ ⊓ M.C₁)).map M.c := by
  apply le_antisymm
  · rintro x ⟨hxS, hxC⟩
    have hxD : x ∈ M.D₀.map M.c := by
      rw [← M.Mz_inf_centralizer]
      exact ⟨M.S_le_Mz hxS, hxC⟩
    obtain ⟨s, hs, rfl⟩ := hxS
    obtain ⟨d, hd, hds⟩ := hxD
    have h1 : M.c (d⁻¹ * s) = 1 := by rw [map_mul, map_inv, hds, inv_mul_cancel]
    obtain ⟨μ, hμ⟩ := M.exists_scalar_of_c_eq_one h1
    have hsd : s = d * (d⁻¹ * s) := by group
    have hsD : s ∈ M.D₀ := by
      rw [hsd]
      exact M.D₀.mul_mem hd (M.scalar_mem_D₀ hμ)
    exact ⟨s, ⟨hs, hsD, M.S₀_le_C₁ hs⟩, rfl⟩
  · rintro _ ⟨s, ⟨hs, hsD, -⟩, rfl⟩
    refine ⟨⟨s, hs, rfl⟩, ?_⟩
    have : M.c s ∈ M.Mz ⊓ Subgroup.centralizer (M.K : Set X) := by
      rw [M.Mz_inf_centralizer]
      exact ⟨s, hsD, rfl⟩
    exact this.2

theorem sylow_facts [Finite F] [Finite X] {p : ℕ} [Fact p.Prime]
    (hS₀ : ¬ 2 ∣ M.S₀.relIndex M.C₁)
    (hK : Nonempty (↥M.K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (he22 : Nat.card ↥M.e22.range = Nat.card ↥(M.D₀ ⊓ M.C₁)) :
    Nat.card ↥(M.S ⊓ M.K) = 2 ^ (Nat.card ↥M.K).factorization 2 ∧
    Nat.card ↥M.S = 2 ^ (Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod p))).factorization 2 *
      Nat.card ↥(M.S ⊓ Subgroup.centralizer (M.K : Set X)) := by
  have hSC := M.S₀_le_C₁
  have h1 := burnsideA315y_card_eq_two_pow (Q := M.S₀ ⊓ M.K₀) (N := M.K₀) inf_le_right
    (M.S₀_two.to_le inf_le_left)
    (burnsideA315y_relIndex_inf_odd hSC M.K₀_le_C₁ M.C₁_le_normalizer_K₀ hS₀)
  have h2 := burnsideA315y_card_eq_two_pow (Q := M.S₀ ⊓ (M.D₀ ⊓ M.C₁)) (N := M.D₀ ⊓ M.C₁)
    inf_le_right (M.S₀_two.to_le inf_le_left)
    (burnsideA315y_relIndex_inf_odd hSC inf_le_right M.C₁_le_normalizer_D₀ hS₀)
  have h3 := burnsideA315y_card_eq_two_pow hSC M.S₀_two hS₀
  have hK₀ : Nat.card ↥M.K₀ = Nat.card (CFSG.GorensteinWalter.PGL2 (ZMod p)) := by
    obtain ⟨e⟩ := hK
    rw [← M.card_K, Nat.card_congr e.toEquiv, burnsideA315y_card_SL2]
  constructor
  · rw [M.S_inf_K, burnsideA315y_card_map_of_ker M.c _ (fun s hs => M.c_S₀_ker (Subgroup.mem_inf.mp hs).1), h1,
      M.card_K]
  · rw [M.S_inf_centralizer, burnsideA315y_card_map_of_ker M.c _ (fun s hs => M.c_S₀_ker (Subgroup.mem_inf.mp hs).1), h2,
      S, burnsideA315y_card_map_of_ker M.c _ (fun s hs => M.c_S₀_ker hs), h3, M.card_C₁, he22, hK₀,
      Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply, pow_add]

theorem sylow_inn [Finite F] {P : Type} [Group P] [Finite P]
    (M : burnsideA315y_Model F (MulAut P))
    (hS₀ : ¬ 2 ∣ M.S₀.relIndex M.C₁) (hC₁ : ¬ 2 ∣ M.C₁.relIndex M.Γ₁)
    (hL : M.L = (MulAut.conj : P →* MulAut P).range)
    (hinj : Function.Injective (MulAut.conj : P →* MulAut P)) :
    ∃ R : Subgroup P, CFSG.QuasithinUnique.IsSylowTwoOf R ⊤ ∧
      M.S = R.map (MulAut.conj : P →* MulAut P) := by
  have hSL : M.S ≤ (MulAut.conj : P →* MulAut P).range := hL ▸ M.S_le_L
  refine ⟨M.S.comap MulAut.conj, ⟨le_top, ?_, ?_⟩, (Subgroup.map_comap_eq_self hSL).symm⟩
  · exact (M.S₀_two.map M.c).comap_of_injective _ hinj
  · change ¬ 2 ∣ (M.S.comap MulAut.conj).relIndex ⊤
    rw [Subgroup.relIndex_top_right, Subgroup.index_comap, ← hL]
    have h2 : M.S.relIndex M.L ∣ M.S₀.relIndex M.Γ₁ :=
      burnsideA315y_relIndex_map_dvd M.c (M.S₀_le_C₁.trans M.C₁_le_Γ₁)
    have h3 : M.S₀.relIndex M.C₁ * M.C₁.relIndex M.Γ₁ = M.S₀.relIndex M.Γ₁ :=
      Subgroup.relIndex_mul_relIndex _ _ _ M.S₀_le_C₁ M.C₁_le_Γ₁
    intro h4
    rw [← h3] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp (h4.trans h2) with h6 | h6
    exacts [hS₀ h6, hC₁ h6]

theorem D₀_cyclic [Finite F] {G' : Type} [Group G'] [IsCyclic G'] [Finite G'] (ψ : G' →* ↥M.Γ)
    (hψ : ∀ g, ψ g ∈ M.D₀) (hsurj : ∀ d ∈ M.D₀, ∃ g, M.c (ψ g) = M.c d) :
    IsCyclic ↥(M.D₀.map M.c) ∧ Nat.card ↥(M.D₀.map M.c) ∣ Nat.card G' := by
  have h1 : M.D₀.map M.c = (M.c.comp ψ).range := by
    ext x
    constructor
    · rintro ⟨d, hd, rfl⟩
      obtain ⟨g, hg⟩ := hsurj d hd
      exact ⟨g, hg⟩
    · rintro ⟨g, rfl⟩
      exact ⟨ψ g, hψ g, rfl⟩
  rw [h1]
  refine ⟨isCyclic_of_surjective (M.c.comp ψ).rangeRestrict
    (M.c.comp ψ).rangeRestrict_surjective, ?_⟩
  rw [← Subgroup.index_ker]
  exact Subgroup.index_dvd_card _

end burnsideA315y_Model

theorem burnsideA315y_conj_injective {G P : Type} [Group G] [Group P] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) (e : ↥L ≃* P) :
    Function.Injective (MulAut.conj : P →* MulAut P) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hc : e.symm x ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 : MulAut.conj x (e g) = e g := by rw [hx]; rfl
    rw [MulAut.conj_apply] at h1
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    calc e g * x = x * e g * x⁻¹ * x := by rw [h1]
      _ = x * e g := by group
  haveI := h.simple
  obtain ⟨a, b, hab⟩ := h.nonabelian
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥L) with hc' | hc'
  · rw [hc', Subgroup.mem_bot] at hc
    have := congrArg e hc
    rwa [e.apply_symm_apply, map_one] at this
  · exfalso
    have hb : b ∈ Subgroup.center ↥L := hc' ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

theorem burnsideA315y_finish' {G P : Type} [Group G] [Group P] [Finite P] {L T B : Subgroup G}
    (h : CFSG.Quasithin.A315Hyp L T B) [L.Normal] (e : ↥L ≃* P)
    {δ : Bool} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hL : CFSG.Quasithin.IsPSLEps3 δ p 1 ↥L)
    {F : Type} [Field F] [Finite F] (M : burnsideA315y_Model F (MulAut P))
    (hfit : burnsideA315y_FittingStatement) (hsteps : burnsideA315y_StepsStatement)
    (hcartan : burnsideA315y_CartanStatement)
    (hS₀ : ¬ 2 ∣ M.S₀.relIndex M.C₁) (hC₁ : ¬ 2 ∣ M.C₁.relIndex M.Γ₁)
    (hLeq : M.L = (MulAut.conj : P →* MulAut P).range)
    (hoddc : ∀ φ : MulAut P, Odd (orderOf φ) → φ ∈ M.c.range)
    (hK : Nonempty (↥M.K ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod p)))
    (hΓscal : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g → ∀ μ : Fˣ,
      (μ : F) = ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 →
        Matrix.GeneralLinearGroup.scalar (Fin 3) μ ∈ M.Γ)
    (hΓdiag : ∀ g : ↥M.Γ, (g : GL (Fin 3) F) * negDiag3 F = negDiag3 F * g →
      ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 → ∀ (n : ℕ) (s : Fˣ),
        (s : F) = (ulBlock ((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)).det ^ n →
          burnsideA315y_dgl s ∈ M.Γ)
    (he22 : Nat.card ↥M.e22.range = Nat.card ↥(M.D₀ ⊓ M.C₁))
    (hΓ₁ : ¬ p ∣ M.Γ₁.index)
    (hD₀cyc : IsCyclic ↥(M.D₀.map M.c))
    (hD₀card : Nat.card ↥(M.D₀.map M.c) ∣ (if δ then p - 1 else p + 1))
    (hU : ∃ U : Subgroup (MulAut P),
      CFSG.Quasithin.A315.IsSylowOf p U (MulAut.conj : P →* MulAut P).range ∧
      M.D₀.map M.c ≤ Subgroup.normalizer (U : Set (MulAut P)))
    (hE : ∀ B' : Subgroup (MulAut P), B' ≤ M.c.range → IsMulCommutative ↥B' →
      Odd (Nat.card ↥B') → ¬ IsPGroup 3 ↥B' →
      (B' : Set (MulAut P)) * (M.S : Set (MulAut P)) =
        (M.S : Set (MulAut P)) * (B' : Set (MulAut P)) → M.DichE B' →
      δ = true ∧ B' ≤ (MulAut.conj : P →* MulAut P).range ∧
        CFSG.Quasithin.IsElemAbelianOfRank p 2 ↥B' ∧
        M.S ≤ Subgroup.normalizer (B' : Set (MulAut P)) ∧ B' ≠ ⊥ ∧
        ∀ C : Subgroup (MulAut P), C ≤ B' → M.S ≤ Subgroup.normalizer (C : Set (MulAut P)) →
          C = ⊥ ∨ C = B')
    (hab : IsMulCommutative ↥B) :
    CFSG.Quasithin.A315Case2 L T B ∨ CFSG.Quasithin.A315Case3 L T B := by
  have hinj := burnsideA315y_conj_injective h e
  obtain ⟨hSK, hScard⟩ := M.sylow_facts hS₀ hK he22
  have hKL : M.K ≤ (MulAut.conj : P →* MulAut P).range := hLeq ▸ M.K_le_L
  have hLc : (MulAut.conj : P →* MulAut P).range ≤ M.c.range :=
    hLeq ▸ Subgroup.map_le_range M.c M.Γ₁
  have hrel : ¬ p ∣ (MulAut.conj : P →* MulAut P).range.relIndex M.c.range := by
    intro hdvd
    apply hΓ₁
    rw [← hLeq] at hdvd
    exact hdvd.trans M.relIndex_L_dvd
  exact burnsideA315y_finish h e hp2 hL M hfit hsteps hcartan (M.sylow_inn hS₀ hC₁ hLeq hinj)
    hoddc hK hΓscal hΓdiag hSK hScard hKL hLc hrel hD₀cyc hD₀card hU hE hab

end CFSG.ASVolI
