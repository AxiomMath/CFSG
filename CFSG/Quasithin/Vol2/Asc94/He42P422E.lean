module

public import CFSG.Quasithin.Vol2.Asc94.He42P422J
public import CFSG.Quasithin.Vol2.Asc94.He42P422Cov
public import CFSG.Quasithin.Vol2.Asc94.He42Spec2
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.Quasithin.A94.He42

open Matrix Subgroup CFSG.Quasithin.A94.HeJ

variable {G : Type} [Group G] [Finite G]

namespace HeSetup

variable (S : HeSetup G)

theorem N_le_normalizer_A'_422 {n : G} (hn : n ∈ S.N) : n ∈ normalizer (S.A' : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (S.hD.hK.norm n hn).2 x hx
  · intro hx
    have h := (S.hD.hK.norm n⁻¹ (S.N.inv_mem hn)).2 _ hx
    have e : n⁻¹ * (n * x * n⁻¹) * n⁻¹⁻¹ = x := by group
    rwa [e] at h

theorem rhoG_inv_422 {n : G} (hn : n ∈ S.N) : S.rhoG n⁻¹ = (S.rhoG n)⁻¹ := by
  rw [S.rhoG_of_mem (S.N.inv_mem hn), S.rhoG_of_mem hn, ← map_inv]
  rfl

theorem K_norm_Z_422 {k : G} (hk : k ∈ S.K) {z : G} (hz : z ∈ S.Z) : k * z * k⁻¹ ∈ S.Z := by
  have hkN : k ∈ S.N := (Subgroup.mem_inf.mp hk).1
  have hz' := Subgroup.mem_inf.mp hz
  exact Subgroup.mem_inf.mpr ⟨(S.hD.hK.norm k hkN).1 z hz'.1, (S.hD.hK.norm k hkN).2 z hz'.2⟩

theorem N_norm_Z_422 {n : G} (hn : n ∈ S.N) {z : G} (hz : z ∈ S.Z) : n * z * n⁻¹ ∈ S.Z := by
  have hz' := Subgroup.mem_inf.mp hz
  exact Subgroup.mem_inf.mpr ⟨(S.hD.hK.norm n hn).1 z hz'.1, (S.hD.hK.norm n hn).2 z hz'.2⟩

theorem B_conj_422 {n : G} (hn : n ∈ S.N) (h2 : (S.rhoG n).2 = 1) (hc : Commute (S.rhoG n).1 S.g) :
    ∀ b ∈ S.B, n * b * n⁻¹ ∈ S.B := by
  intro b hb
  have hbm := (S.hD.mem_B_iff S.hxN S.hxa S.hx3).1 hb
  have hbZ : b ∈ S.A ⊓ S.A' := hbm.1
  have hnZ : n * b * n⁻¹ ∈ S.A ⊓ S.A' := S.N_norm_Z_422 hn hbZ
  have hm := S.m_conj_422 hn hbZ
  rw [h2] at hm
  simp only [Units.val_one, Matrix.transpose_one, mul_one] at hm
  have hPg : ((S.rhoG n).1 : M2) * (S.g : M2) = (S.g : M2) * ((S.rhoG n).1 : M2) := by
    have h := congrArg Units.val hc.eq
    rwa [Units.val_mul, Units.val_mul] at h
  refine (S.hD.mem_B_iff S.hxN S.hxa S.hx3).2 ⟨hnZ, ?_⟩
  rw [hm]
  have hcm : (S.g : M2) * S.m b = S.m b * (S.g : M2) := hbm.2
  calc (S.g : M2) * (((S.rhoG n).1 : M2) * S.m b)
      = ((S.g : M2) * ((S.rhoG n).1 : M2)) * S.m b := by rw [mul_assoc]
    _ = (((S.rhoG n).1 : M2) * (S.g : M2)) * S.m b := by rw [hPg]
    _ = ((S.rhoG n).1 : M2) * ((S.g : M2) * S.m b) := by rw [mul_assoc]
    _ = ((S.rhoG n).1 : M2) * (S.m b * (S.g : M2)) := by rw [hcm]
    _ = (((S.rhoG n).1 : M2) * S.m b) * (S.g : M2) := by rw [mul_assoc]

theorem L2_conj_422 {n : G} (hn : n ∈ S.N) (h2 : (S.rhoG n).2 = 1) (hc : Commute (S.rhoG n).1 S.g) :
    ∀ h ∈ S.L2, n * h * n⁻¹ ∈ S.L2 := by
  intro h hh
  obtain ⟨hhA, hhB⟩ := Subgroup.mem_inf.mp hh
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (S.N_le_normalizer_A'_422 hn) hhA)
      (Subgroup.inv_mem _ (S.N_le_normalizer_A'_422 hn))
  · rw [mem_centralizer_iff]
    intro b hb
    have h2' : (S.rhoG n⁻¹).2 = 1 := by
      rw [S.rhoG_inv_422 hn, Prod.snd_inv, h2, inv_one]
    have hc' : Commute (S.rhoG n⁻¹).1 S.g := by
      rw [S.rhoG_inv_422 hn]
      exact hc.inv_left
    have hb' : n⁻¹ * b * n⁻¹⁻¹ ∈ S.B := S.B_conj_422 (S.N.inv_mem hn) h2' hc' b hb
    have hcomm := mem_centralizer_iff.mp hhB _ hb'
    calc b * (n * h * n⁻¹) = n * ((n⁻¹ * b * n⁻¹⁻¹) * h) * n⁻¹ := by group
      _ = n * (h * (n⁻¹ * b * n⁻¹⁻¹)) * n⁻¹ := by rw [hcomm]
      _ = n * h * n⁻¹ * b := by group

theorem B_le_conjZ_422 {g : G} (hg : g ∈ S.L2) : S.B ≤ S.conjZ_422 g := by
  intro b hb
  have hB := S.baseFacts
  have hbZ : b ∈ S.Z := (Subgroup.mem_inf.mp hb).1
  have hcomm : b * g = g * b := mem_centralizer_iff.mp (hB.L2_le_centralizer hg) b hb
  exact (mem_conjZ_422 S).mpr ⟨b, hbZ, (mul_inv_eq_iff_eq_mul).2 hcomm.symm⟩

theorem conjZ_mem_iff_422 {g x : G} : x ∈ S.conjZ_422 g ↔ g⁻¹ * x * g ∈ S.Z := by
  rw [mem_conjZ_422]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have e : g⁻¹ * (g * z * g⁻¹) * g = z := by group
    rwa [e]
  · intro h
    exact ⟨g⁻¹ * x * g, h, by group⟩

theorem conjZ_le_of_K_422 {g g' : G} (hk : g⁻¹ * g' ∈ S.K) : S.conjZ_422 g' ≤ S.conjZ_422 g := by
  intro x hx
  rw [conjZ_mem_iff_422] at hx ⊢
  have e : g⁻¹ * x * g = (g⁻¹ * g') * (g'⁻¹ * x * g') * (g⁻¹ * g')⁻¹ := by group
  rw [e]
  exact S.K_norm_Z_422 hk hx

theorem E_fwd_422 {y₁ y₂ : G} (hZm : S.StepZmat y₁ y₂) (hn : y₁ ∈ S.N) (h2 : (S.rhoG y₁).2 = 1)
    (hc : Commute (S.rhoG y₁).1 S.g)
    (hSp : ∀ g ∈ S.L2, g ∉ S.K → ∀ z ∈ S.Z, g * z * g⁻¹ ∈ S.Z → z ∈ S.B)
    {g : G} (hg : g ∈ S.L2) {τ : G} (hτ : τ ∈ S.conjZ_422 g) (hτB : τ ∉ S.B) (hτy : y₁ * τ = τ * y₁) :
    ∀ e ∈ S.conjZ_422 g, y₁ * e * y₁⁻¹ ∈ S.conjZ_422 g := by
  intro e he
  obtain ⟨z, hz, rfl⟩ := (mem_conjZ_422 S).mp he
  have hg' : y₁ * g * y₁⁻¹ ∈ S.L2 := S.L2_conj_422 hn h2 hc g hg
  have hyz : y₁ * z * y₁⁻¹ ∈ S.Z := hZm.1 y₁ (Set.mem_insert _ _) z hz
  have hfix : y₁ * τ * y₁⁻¹ = τ := (mul_inv_eq_iff_eq_mul).2 hτy
  have hτ' : τ ∈ S.conjZ_422 (y₁ * g * y₁⁻¹) := by
    obtain ⟨z₀, hz₀, hτz⟩ := (mem_conjZ_422 S).mp hτ
    have hyz₀ : y₁ * z₀ * y₁⁻¹ ∈ S.Z := hZm.1 y₁ (Set.mem_insert _ _) z₀ hz₀
    refine (mem_conjZ_422 S).mpr ⟨y₁ * z₀ * y₁⁻¹, hyz₀, ?_⟩
    calc y₁ * g * y₁⁻¹ * (y₁ * z₀ * y₁⁻¹) * (y₁ * g * y₁⁻¹)⁻¹ = y₁ * (g * z₀ * g⁻¹) * y₁⁻¹ := by
          group
      _ = y₁ * τ * y₁⁻¹ := by rw [hτz]
      _ = τ := hfix
  have hk : g⁻¹ * (y₁ * g * y₁⁻¹) ∈ S.K := pair_422 S hSp hg' hg hτ' hτ hτB
  have he' : y₁ * (g * z * g⁻¹) * y₁⁻¹ ∈ S.conjZ_422 (y₁ * g * y₁⁻¹) := by
    refine (mem_conjZ_422 S).mpr ⟨y₁ * z * y₁⁻¹, hyz, ?_⟩
    group
  exact S.conjZ_le_of_K_422 hk he'

theorem E_bwd_422 {y₁ : G} (hy3 : y₁ ^ 3 = 1) {g : G}
    (hfwd : ∀ e ∈ S.conjZ_422 g, y₁ * e * y₁⁻¹ ∈ S.conjZ_422 g) :
    ∀ e ∈ S.conjZ_422 g, y₁⁻¹ * e * y₁ ∈ S.conjZ_422 g := by
  have h3 : y₁ * y₁ * y₁ = 1 := by
    have h := hy3
    simp only [pow_succ, pow_zero, one_mul] at h
    exact h
  have hF3 : ∀ w : G, y₁ * (y₁ * (y₁ * w * y₁⁻¹) * y₁⁻¹) * y₁⁻¹ = w := by
    intro w
    calc y₁ * (y₁ * (y₁ * w * y₁⁻¹) * y₁⁻¹) * y₁⁻¹ = (y₁ * y₁ * y₁) * w * (y₁ * y₁ * y₁)⁻¹ := by
          group
      _ = w := by rw [h3]; group
  intro e he
  have hFW : y₁ * (y₁⁻¹ * e * y₁) * y₁⁻¹ = e := by group
  have hW : y₁⁻¹ * e * y₁ = y₁ * (y₁ * e * y₁⁻¹) * y₁⁻¹ := by
    calc y₁⁻¹ * e * y₁ = y₁ * (y₁ * (y₁ * (y₁⁻¹ * e * y₁) * y₁⁻¹) * y₁⁻¹) * y₁⁻¹ :=
          (hF3 _).symm
      _ = y₁ * (y₁ * e * y₁⁻¹) * y₁⁻¹ := by rw [hFW]
  rw [hW]
  exact hfwd _ (hfwd e he)

theorem comm_conj_iff_422 {g z y₁ : G} :
    (g * z * g⁻¹) * y₁ = y₁ * (g * z * g⁻¹) ↔ z * (g⁻¹ * y₁ * g) = (g⁻¹ * y₁ * g) * z := by
  constructor
  · intro h
    calc z * (g⁻¹ * y₁ * g) = g⁻¹ * ((g * z * g⁻¹) * y₁) * g := by group
      _ = g⁻¹ * (y₁ * (g * z * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * y₁ * g) * z := by group
  · intro h
    calc (g * z * g⁻¹) * y₁ = g * (z * (g⁻¹ * y₁ * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y₁ * g) * z) * g⁻¹ := by rw [h]
      _ = y₁ * (g * z * g⁻¹) := by group

theorem card_conjZ_centralizer_422 {y₁ : G} (g : G) :
    Nat.card ↥(S.conjZ_422 g ⊓ centralizer ({y₁} : Set G)) =
      Nat.card ↥(S.Z ⊓ centralizer ({g⁻¹ * y₁ * g} : Set G)) := by
  have hmap : S.conjZ_422 g ⊓ centralizer ({y₁} : Set G) =
      (S.Z ⊓ centralizer ({g⁻¹ * y₁ * g} : Set G)).map (MulAut.conj g).toMonoidHom := by
    ext c
    constructor
    · rintro ⟨hc1, hc2⟩
      obtain ⟨z, hz, rfl⟩ := (mem_conjZ_422 S).mp hc1
      refine (Subgroup.mem_map).mpr ⟨z, Subgroup.mem_inf.mpr ⟨hz, ?_⟩, ?_⟩
      · rw [mem_centralizer_singleton_iff]
        exact (comm_conj_iff_422.mp (mem_centralizer_singleton_iff.mp hc2))
      · simp [MulAut.conj_apply]
    · intro hc
      obtain ⟨c', hc', rfl⟩ := Subgroup.mem_map.mp hc
      obtain ⟨hz, hcy⟩ := Subgroup.mem_inf.mp hc'
      rw [mem_centralizer_singleton_iff] at hcy
      refine Subgroup.mem_inf.mpr ⟨(mem_conjZ_422 S).mpr ⟨c', hz, ?_⟩, ?_⟩
      · simp [MulAut.conj_apply]
      · rw [mem_centralizer_singleton_iff]
        simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
        exact comm_conj_iff_422.mpr hcy
  rw [hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem rhoG_pow_three_422 {y : G} (hyN : y ∈ S.N) (hy3 : y ^ 3 = 1) : S.rhoG y ^ 3 = 1 := by
  rw [S.rhoG_of_mem hyN, ← map_pow]
  have h3 : (⟨y, hyN⟩ : ↥S.N) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
  rw [h3, map_one]

theorem card_Z_centralizer_422 {y : G} (hyN : y ∈ S.N) (hyZ : ∀ w ∈ S.Z, y * w * y⁻¹ ∈ S.Z) :
    Nat.card ↥(S.Z ⊓ centralizer ({y} : Set G)) =
      (Finset.univ.filter (fun M : M2 => ((S.rhoG y).1 : M2) * M * ((S.rhoG y).2 : M2)ᵀ = M)).card := by
  have hf : ∀ c : ↥(S.Z ⊓ centralizer ({y} : Set G)),
      ((S.rhoG y).1 : M2) * S.m c.1 * ((S.rhoG y).2 : M2)ᵀ = S.m c.1 := by
    intro c
    have hcZ : c.1 ∈ S.Z := (Subgroup.mem_inf.mp c.2).1
    have hcy : c.1 * y = y * c.1 := mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp c.2).2
    have hyc : y * c.1 * y⁻¹ = c.1 := (mul_inv_eq_iff_eq_mul).2 hcy.symm
    have h := S.m_conj_422 hyN hcZ
    rw [hyc] at h
    exact h.symm
  let F : ↥(S.Z ⊓ centralizer ({y} : Set G)) →
      {M : M2 // ((S.rhoG y).1 : M2) * M * ((S.rhoG y).2 : M2)ᵀ = M} :=
    fun c => ⟨S.m c.1, hf c⟩
  have hinj : Function.Injective F := by
    intro c d h
    have h1 : S.m c.1 = S.m d.1 := congrArg Subtype.val h
    apply Subtype.ext
    exact S.hD.hT.minj _ (Subgroup.mem_inf.mp c.2).1 _ (Subgroup.mem_inf.mp d.2).1 h1
  have hsurj : Function.Surjective F := by
    intro M
    obtain ⟨z, hz, hzM⟩ := S.hD.hT.msurj M.1
    have hzy : y * z * y⁻¹ = z := by
      apply S.hD.hT.minj _ (hyZ z hz) _ hz
      rw [S.m_conj_422 hyN hz, hzM]
      exact M.2
    have hzC : z ∈ centralizer ({y} : Set G) :=
      mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.1 hzy).symm
    exact ⟨⟨z, Subgroup.mem_inf.mpr ⟨hz, hzC⟩⟩, Subtype.ext hzM⟩
  have e := Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩)
  rw [e, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem R_le_conjZ_422 {y₁ y₂ : G} (hZm : S.StepZmat y₁ y₂) (hn : y₁ ∈ S.N) (h2 : (S.rhoG y₁).2 = 1)
    (hc : Commute (S.rhoG y₁).1 S.g)
    (hSp : ∀ g ∈ S.L2, g ∉ S.K → ∀ z ∈ S.Z, g * z * g⁻¹ ∈ S.Z → z ∈ S.B)
    (hJ : ∀ c : G, (∀ w ∈ S.Z, w * c = c * w) → c ∈ S.J)
    (hy₁ord : orderOf y₁ = 3)
    (hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4)
    (hRA : S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) = ⊥)
    {g : G} (hg : g ∈ S.L2) {τ : G} (hτR : τ ∈ S.A' ⊓ centralizer ({y₁} : Set G)) (hτ1 : τ ≠ 1)
    (hτ : τ ∈ S.conjZ_422 g) :
    S.A' ⊓ centralizer ({y₁} : Set G) ≤ S.conjZ_422 g := by
  have hB := S.baseFacts
  have hτB : τ ∉ S.B := by
    intro hτB
    have hτA : τ ∈ S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) :=
      ⟨(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hτB).1).1, hτR⟩
    rw [hRA, Subgroup.mem_bot] at hτA
    exact hτ1 hτA
  have hτy : y₁ * τ = τ * y₁ :=
    (mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hτR).2).symm
  have hfwd := S.E_fwd_422 hZm hn h2 hc hSp hg hτ hτB hτy
  have hy₁3 : y₁ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₁
    rwa [hy₁ord] at h
  have hbwd := S.E_bwd_422 hy₁3 hfwd
  obtain ⟨y, hy⟩ : ∃ y : G, y = g⁻¹ * y₁ * g := ⟨_, rfl⟩
  have hyZ : ∀ w ∈ S.Z, y * w * y⁻¹ ∈ S.Z := by
    intro w hw
    have h := (S.conjZ_mem_iff_422).mp (hfwd (g * w * g⁻¹) ((mem_conjZ_422 S).mpr ⟨w, hw, rfl⟩))
    have e : g⁻¹ * (y₁ * (g * w * g⁻¹) * y₁⁻¹) * g = y * w * y⁻¹ := by rw [hy]; group
    rwa [e] at h
  have hyZ' : ∀ w ∈ S.Z, y⁻¹ * w * y ∈ S.Z := by
    intro w hw
    have h := (S.conjZ_mem_iff_422).mp (hbwd (g * w * g⁻¹) ((mem_conjZ_422 S).mpr ⟨w, hw, rfl⟩))
    have e : g⁻¹ * (y₁⁻¹ * (g * w * g⁻¹) * y₁) * g = y⁻¹ * w * y := by rw [hy]; group
    rwa [e] at h
  have hyN : y ∈ S.N := mem_N_of_normalizes_Z_422 S hyZ hyZ' hJ
  have hy3 : y ^ 3 = 1 := by
    rw [hy, show g⁻¹ * y₁ * g = g⁻¹ * y₁ * g⁻¹⁻¹ by group, conj_pow, hy₁3]
    group
  have hyord : orderOf y = 3 := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y₁
    have h' : orderOf (g⁻¹ * y₁ * g) = orderOf y₁ := by simpa [MulAut.conj_apply] using h
    rw [hy, h', hy₁ord]
  have hρy : S.rhoG y ≠ 1 := S.rhoG_ne_one_422 hyN hyord
  have hpow := S.rhoG_pow_three_422 hyN hy3
  have hP3 : (S.rhoG y).1 ^ 3 = 1 := by simpa using congrArg Prod.fst hpow
  have hQ3 : (S.rhoG y).2 ^ 3 = 1 := by simpa using congrArg Prod.snd hpow
  have hPQ : (S.rhoG y).1 ≠ 1 ∨ (S.rhoG y).2 ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hρy (Prod.ext hcon.1 hcon.2)
  have hfin := he42p_fin_cnt_422 (S.rhoG y).1 (S.rhoG y).2 hP3 hQ3 hPQ
  have hCE := S.card_conjZ_centralizer_422 (y₁ := y₁) g
  rw [← hy] at hCE
  have hCZ := S.card_Z_centralizer_422 hyN hyZ
  have hτCE : τ ∈ S.conjZ_422 g ⊓ centralizer ({y₁} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hτ, (Subgroup.mem_inf.mp hτR).2⟩
  haveI : Nontrivial ↥(S.conjZ_422 g ⊓ centralizer ({y₁} : Set G)) :=
    ⟨⟨⟨τ, hτCE⟩, 1, fun h => hτ1 (congrArg Subtype.val h)⟩⟩
  have hgt : 1 < Nat.card ↥(S.conjZ_422 g ⊓ centralizer ({y₁} : Set G)) := Finite.one_lt_card
  have hcount : Nat.card ↥(S.conjZ_422 g ⊓ centralizer ({y₁} : Set G)) = 4 := by
    have hmem := hfin
    rw [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h4
    · exfalso
      rw [hCE, hCZ, h1] at hgt
      exact lt_irrefl _ hgt
    · rw [hCE, hCZ, h4]
  have hCE_le : (S.conjZ_422 g ⊓ centralizer ({y₁} : Set G)) ≤ S.A' ⊓ centralizer ({y₁} : Set G) := by
    intro c hc
    obtain ⟨hcE, hcy⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨z, hz, hzc⟩ := (mem_conjZ_422 S).mp hcE
    have hgN : g ∈ normalizer (S.A' : Set G) := hB.L2_le_normalizer hg
    have hA' : c ∈ S.A' := by
      rw [← hzc]
      exact (Subgroup.mem_normalizer_iff.mp hgN z).mp (Subgroup.mem_inf.mp hz).2
    exact Subgroup.mem_inf.mpr ⟨hA', hcy⟩
  have hEq : (S.conjZ_422 g ⊓ centralizer ({y₁} : Set G)) = S.A' ⊓ centralizer ({y₁} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hCE_le (le_of_eq (by rw [hR4, hcount]))
  calc S.A' ⊓ centralizer ({y₁} : Set G) = (S.conjZ_422 g ⊓ centralizer ({y₁} : Set G)) := hEq.symm
    _ ≤ S.conjZ_422 g := inf_le_left

theorem factor_R_B_422 {y₁ g : G} (hg : g ∈ S.L2)
    (hR4 : Nat.card ↥(S.A' ⊓ centralizer ({y₁} : Set G)) = 4)
    (hRA : S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) = ⊥)
    (hRE : S.A' ⊓ centralizer ({y₁} : Set G) ≤ S.conjZ_422 g)
    {v : G} (hv : v ∈ S.conjZ_422 g) :
    ∃ r ∈ S.A' ⊓ centralizer ({y₁} : Set G), ∃ β ∈ S.B, v = r * β := by
  have hB := S.baseFacts
  have hBE : S.B ≤ S.conjZ_422 g := S.B_le_conjZ_422 hg
  have hBA : ∀ b ∈ S.B, b ∈ S.A := fun b hb => (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hb).1).1
  let φ : ↥(S.A' ⊓ centralizer ({y₁} : Set G)) × ↥S.B → ↥(S.conjZ_422 g) :=
    fun p => ⟨p.1.1 * p.2.1, (S.conjZ_422 g).mul_mem (hRE p.1.2) (hBE p.2.2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨⟨r, hr⟩, ⟨β, hβ⟩⟩ ⟨⟨r', hr'⟩, ⟨β', hβ'⟩⟩ h
    have h1 : r * β = r' * β' := congrArg Subtype.val h
    have hmem : r'⁻¹ * r ∈ S.A ⊓ (S.A' ⊓ centralizer ({y₁} : Set G)) := by
      refine Subgroup.mem_inf.mpr ⟨?_, (S.A' ⊓ centralizer ({y₁} : Set G)).mul_mem
        ((S.A' ⊓ centralizer ({y₁} : Set G)).inv_mem hr') hr⟩
      have e : r'⁻¹ * r = β' * β⁻¹ := by
        calc r'⁻¹ * r = r'⁻¹ * (r * β) * β⁻¹ := by group
          _ = r'⁻¹ * (r' * β') * β⁻¹ := by rw [h1]
          _ = β' * β⁻¹ := by group
      rw [e]
      exact S.A.mul_mem (hBA β' hβ') (S.A.inv_mem (hBA β hβ))
    rw [hRA, Subgroup.mem_bot] at hmem
    have hrr : r' = r := inv_mul_eq_one.mp hmem
    subst hrr
    have hββ : β = β' := mul_left_cancel h1
    subst hββ
    rfl
  have hcard : Nat.card ↥(S.conjZ_422 g) ≤
      Nat.card (↥(S.A' ⊓ centralizer ({y₁} : Set G)) × ↥S.B) :=
    le_of_eq (by rw [Nat.card_prod, S.card_conjZ_422 g, hR4, hB.card_B])
  have hbij := Function.Injective.bijective_of_nat_card_le hinj hcard
  obtain ⟨⟨⟨r, hr⟩, ⟨β, hβ⟩⟩, hp⟩ := hbij.2 ⟨v, hv⟩
  exact ⟨r, hr, β, hβ, (congrArg Subtype.val hp).symm⟩

theorem y_conj_N_422 {y₁ y₂ : G} (hZm : S.StepZmat y₁ y₂) (hn : y₁ ∈ S.N) (h2 : (S.rhoG y₁).2 = 1)
    (hc : Commute (S.rhoG y₁).1 S.g)
    (hSp : ∀ g ∈ S.L2, g ∉ S.K → ∀ z ∈ S.Z, g * z * g⁻¹ ∈ S.Z → z ∈ S.B)
    (hJ : ∀ c : G, (∀ w ∈ S.Z, w * c = c * w) → c ∈ S.J)
    (hy₁ord : orderOf y₁ = 3)
    {g : G} (hg : g ∈ S.L2) {τ : G} (hτ : τ ∈ S.conjZ_422 g) (hτB : τ ∉ S.B) (hτy : y₁ * τ = τ * y₁) :
    g⁻¹ * y₁ * g ∈ S.N ∧ orderOf (g⁻¹ * y₁ * g) = 3 := by
  have hfwd := S.E_fwd_422 hZm hn h2 hc hSp hg hτ hτB hτy
  have hy₁3 : y₁ ^ 3 = 1 := by
    have h := pow_orderOf_eq_one y₁
    rwa [hy₁ord] at h
  have hbwd := S.E_bwd_422 hy₁3 hfwd
  obtain ⟨y, hy⟩ : ∃ y : G, y = g⁻¹ * y₁ * g := ⟨_, rfl⟩
  have hyZ : ∀ w ∈ S.Z, y * w * y⁻¹ ∈ S.Z := by
    intro w hw
    have h := (S.conjZ_mem_iff_422).mp (hfwd (g * w * g⁻¹) ((mem_conjZ_422 S).mpr ⟨w, hw, rfl⟩))
    have e : g⁻¹ * (y₁ * (g * w * g⁻¹) * y₁⁻¹) * g = y * w * y⁻¹ := by rw [hy]; group
    rwa [e] at h
  have hyZ' : ∀ w ∈ S.Z, y⁻¹ * w * y ∈ S.Z := by
    intro w hw
    have h := (S.conjZ_mem_iff_422).mp (hbwd (g * w * g⁻¹) ((mem_conjZ_422 S).mpr ⟨w, hw, rfl⟩))
    have e : g⁻¹ * (y₁⁻¹ * (g * w * g⁻¹) * y₁) * g = y⁻¹ * w * y := by rw [hy]; group
    rwa [e] at h
  have hyN : y ∈ S.N := mem_N_of_normalizes_Z_422 S hyZ hyZ' hJ
  have hyord : orderOf y = 3 := by
    have h := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective y₁
    have h' : orderOf (g⁻¹ * y₁ * g) = orderOf y₁ := by simpa [MulAut.conj_apply] using h
    rw [hy, h', hy₁ord]
  rw [← hy]
  exact ⟨hyN, hyord⟩

end HeSetup

end CFSG.Quasithin.A94.He42
