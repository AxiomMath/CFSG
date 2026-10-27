module

public import CFSG.Quasithin.Background.F6NQStructure
public import CFSG.Quasithin.EmptyFaithful.S14110AuxS4
public import CFSG.Quasithin.Background.F6CatDickson

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.GorensteinWalter

namespace F6

theorem nonempty_dihedral_of_inverting {G : Type*} [Group G] [Finite G] {a h : G}
    (ha2 : a ^ 2 = 1) (hinv : a * h * a⁻¹ = h⁻¹) (hane : a ∉ Subgroup.zpowers h) :
    Nonempty (↥(Subgroup.zpowers h ⊔ Subgroup.zpowers a) ≃* DihedralGroup (orderOf h)) := by
  set S := Subgroup.zpowers h ⊔ Subgroup.zpowers a with hS
  have hhS : h ∈ S := (le_sup_left : Subgroup.zpowers h ≤ S) (Subgroup.mem_zpowers h)
  have haS : a ∈ S := (le_sup_right : Subgroup.zpowers a ≤ S) (Subgroup.mem_zpowers a)
  set ρ : S := ⟨h, hhS⟩ with hρ
  set σ : S := ⟨a, haS⟩ with hσ
  have hgen : (⊤ : Subgroup S) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    apply Subgroup.map_injective S.subtype_injective
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
    simp [hρ, hσ, hS]
  have hσ2 : σ ^ 2 = 1 := Subtype.ext (by simpa using ha2)
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := Subtype.ext (by simpa using hinv)
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    intro hmem
    apply hane
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨e⟩ := CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hρo : orderOf ρ = orderOf h := by rw [hρ, Subgroup.orderOf_mk]
  rw [hρo] at e
  exact ⟨e⟩

theorem dihedral_four_outside : ∀ a b : DihedralGroup 4, a ^ 2 ≠ 1 → b ≠ 1 → b ≠ a →
    b ≠ a ^ 2 → b ≠ a ^ 3 → b ^ 2 = 1 ∧ b * a * b⁻¹ = a⁻¹ := by
  decide

theorem sq_mod_sixteen {p : ℕ} (hp : p % 8 = 3 ∨ p % 8 = 5) : p ^ 2 % 16 = 9 := by
  have h1 : p ^ 2 % 16 = (p % 16) ^ 2 % 16 := Nat.pow_mod p 2 16
  have h2 : p % 16 < 16 := Nat.mod_lt _ (by norm_num)
  have h3 : p % 8 = p % 16 % 8 := (Nat.mod_mod_of_dvd p (by norm_num)).symm
  rw [h1]
  rw [h3] at hp
  interval_cases (p % 16) <;> simp_all

namespace F617L2

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D} {F : Type} [Field F]
  [Finite F] {p : ℕ}

theorem rho_comp_injective_right (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F) :
    Function.Injective ((hT.rho eK).comp G₂.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_rho] at hg
  have h1 : (g : D) ∈ G₂ ⊓ Subgroup.centralizer (K : Set D) := ⟨g.2, hg⟩
  rw [hT.inf_centralizer_eq_bot, Subgroup.mem_bot] at h1
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

theorem rho_injOn {H : Subgroup D} (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F) (hH : H ≤ G₂) :
    Function.Injective ((hT.rho eK).comp H.subtype) := fun a b hab => by
  have := hT.rho_comp_injective_right eK (a₁ := ⟨a, hH a.2⟩) (a₂ := ⟨b, hH b.2⟩) hab
  exact Subtype.ext (congrArg (Subtype.val : ↥G₂ → D) this)

theorem nonempty_inf_mulEquiv_dihedral
    (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F) :
    Nonempty (↥(G₁ ⊓ G₂) ≃* DihedralGroup 4) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT.triple
  have hodd := hT.isOddPrimePower
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set T := G₁ ⊓ G₂ with hTdef
  set f := (hT.rho eK).comp T.subtype with hf
  have hinj : Function.Injective f := hT.rho_injOn eK inf_le_right
  obtain ⟨-, -, hT8⟩ := hT.inf_inf_eq eK
  set R := T.map (hT.rho eK) with hR
  let ι : ↥T ≃* ↥R := (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr (by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]))
  have hR8 : Nat.card R = 8 := by
    rw [← Nat.card_congr ι.toEquiv, hT8]
  have hR2 : IsPGroup 2 R := h.isPGroup_inf.map (hT.rho eK)
  have hidx : ¬ 2 ∣ R.index := by
    intro h2
    have h1 := R.card_mul_index
    rw [hR8, pgl2_card_formula F, hT.card_field] at h1
    have h16 : 16 ∣ p * (p ^ 2 - 1) := by
      rw [← h1]
      exact Nat.mul_dvd_mul_left 8 h2
    have hcop : Nat.Coprime 16 p :=
      Nat.Coprime.pow_left 4 (Nat.coprime_two_left.mpr (hT.prime.odd_of_ne_two
        (by have := hT.five_le; omega)))
    have h16' := hcop.dvd_of_dvd_mul_left h16
    have h9 := sq_mod_sixteen hT.mod_eight
    have : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hT.prime.pos
    omega
  set S : Sylow 2 (PGL2 F) := hR2.toSylow hidx with hS
  obtain ⟨m, -, ⟨e⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model F hodd S
  have hm : 2 ^ m = 4 := by
    have h1 := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at h1
    have h2 : Nat.card ↥(S : Subgroup (PGL2 F)) = 8 := hR8
    omega
  rw [hm] at e
  exact ⟨ι.trans e⟩


theorem false_of_kleinFour_commute
    (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F)
    {V : Subgroup D} (hVG : V ≤ G₂) (hV4 : Nat.card ↥V = 4) (hVsq : ∀ v ∈ V, v * v = 1)
    {x : D} (hxK : x ∈ K) (hxo : orderOf x = 3) (hc : ∀ v ∈ V, v * x = x * v) : False := by
  have hodd := hT.isOddPrimePower
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  set f := (hT.rho eK).comp V.subtype with hf
  have hfinj : Function.Injective f := hT.rho_injOn eK hVG
  set V' := V.map (hT.rho eK) with hV'
  have hVeq : f.range = V' := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
  have hV'4 : Nat.card ↥V' = 4 := by
    rw [← hVeq, ← Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv, hV4]
  have hVK : IsKleinFour ↥V' := by
    refine isKleinFour_of_card_four_of_mul_self hV'4 fun ⟨_, v, hv, rfl⟩ => Subtype.ext ?_
    rw [Subgroup.coe_mul, ← map_mul, Subgroup.coe_one, hVsq v hv, map_one]
  set A := Subgroup.zpowers (hT.rho eK x) with hA
  have hρx : orderOf (hT.rho eK x) = 3 := by
    rw [← hxo]
    have h1 : hT.rho eK x = (hT.rho eK).comp K.subtype ⟨x, hxK⟩ := rfl
    rw [h1, orderOf_injective _ (hT.rho_comp_injective eK)]
    exact Subgroup.orderOf_mk x hxK
  have hAcard : Nat.card ↥A = 3 := by rw [hA, Nat.card_zpowers, hρx]
  refine pgl2_no_kleinFour_centralizes_odd_cyclic F hodd A V' inferInstance ?_ ?_ hVK ?_
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hAcard
    omega
  · rw [hAcard]
    decide
  · rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    change hT.rho eK x ^ k * hT.rho eK v = hT.rho eK v * hT.rho eK x ^ k
    rw [← map_zpow, ← map_mul, ← map_mul]
    congr 1
    exact ((Commute.zpow_left (show Commute x v from (hc v hv).symm) k)).eq

theorem commute_iff_conj_eq {G : Type*} [Group G] {g x : G} : g * x = x * g ↔ g * x * g⁻¹ = x :=
  ⟨fun h => by rw [h, mul_assoc, mul_inv_cancel, mul_one], fun h => by
    calc g * x = g * x * g⁻¹ * g := by group
      _ = x * g := by rw [h]⟩

theorem nonempty_left_mulEquiv_dihedral
    (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F) :
    Nonempty (↥G₁ ≃* DihedralGroup 12) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT.triple
  have hodd := hT.isOddPrimePower
  have : Finite (PGL2 F) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨-, -, hT8⟩ := hT.inf_inf_eq eK
  obtain ⟨eT⟩ := hT.nonempty_inf_mulEquiv_dihedral eK
  set T := G₁ ⊓ G₂ with hTdef
  obtain ⟨x, hxL, hxo, -, -⟩ := hT.exists_generator
  set L₁ := twoResidual G₁ with hL₁
  have hxG : x ∈ G₁ := twoResidual_le G₁ hxL
  have hx1 : x ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hxo; norm_num at hxo
  have hx3 : x ^ 3 = 1 := hxo ▸ pow_orderOf_eq_one x
  have hxx : x⁻¹ ≠ x := by
    intro h1
    have h2 : x ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h1]; exact inv_mul_cancel x
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hxo] at this
    norm_num at this
  have hconj : ∀ t ∈ G₁, t * x * t⁻¹ = x ∨ t * x * t⁻¹ = x⁻¹ := by
    intro t ht
    have hmem := (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual G₁ ht) x).mp hxL
    rcases mem_of_card_eq_three hT.card_left hxL hx1 hmem with h1 | h1 | h1
    · exfalso
      apply hx1
      calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
        _ = 1 := by rw [h1]; group
    · exact Or.inl h1
    · exact Or.inr h1
  obtain ⟨s, hsT, hsx⟩ : ∃ s ∈ T, s * x * s⁻¹ = x⁻¹ := by
    obtain ⟨t, ht, hinv⟩ := F617Setting.exists_inv_mod_pCoreOf h hxG hx3
    have htx : t * x * t⁻¹ = x⁻¹ := by
      rcases hconj t ht with h1 | h1
      · exfalso
        rw [h1] at hinv
        obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 G₁) ⟨_, hinv⟩
        have hk' : (x * x) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
        have h3 : (x * x) ^ 3 = 1 := by
          rw [← pow_two, ← pow_mul, mul_comm, pow_mul, hx3, one_pow]
        have hxx1 : x * x = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
          (Nat.Coprime.pow_left k (by norm_num)) (orderOf_dvd_of_pow_eq_one hk')
          (orderOf_dvd_of_pow_eq_one h3))
        exact hxx (inv_eq_of_mul_eq_one_right hxx1)
      · exact h1
    have ht' : t ∈ ((T ⊔ L₁ : Subgroup D) : Set D) := by
      rw [hTdef, inf_sup_twoResidual_left h]
      exact ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (inf_le_left.trans (le_normalizer_twoResidual G₁))] at ht'
    obtain ⟨τ, hτ, l, hl, hτl⟩ := ht'
    simp only at hτl
    have hlx : l * x * l⁻¹ = x := by
      rcases mem_of_card_eq_three hT.card_left hxL hx1 hl with rfl | rfl | rfl
      · simp
      · group
      · group
    refine ⟨τ, hτ, ?_⟩
    calc τ * x * τ⁻¹ = τ * (l * x * l⁻¹) * τ⁻¹ := by rw [hlx]
      _ = t * x * t⁻¹ := by rw [← hτl]; group
      _ = x⁻¹ := htx
  set C := T ⊓ Subgroup.centralizer ({x} : Set D) with hC
  have hmemC : ∀ g ∈ T, g ∈ C ↔ g * x * g⁻¹ = x := by
    intro g hg
    rw [hC, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    simp only [Set.mem_singleton_iff, forall_eq]
    rw [eq_comm, commute_iff_conj_eq]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨hg, h1⟩⟩
  have hidx : (C.subgroupOf T).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨s, hsT⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul]
    rw [hmemC _ (T.mul_mem b.2 hsT), hmemC _ b.2]
    have hbs : (b : D) * s * x * ((b : D) * s)⁻¹ = ((b : D) * x * (b : D)⁻¹)⁻¹ := by
      calc (b : D) * s * x * ((b : D) * s)⁻¹ = (b : D) * (s * x * s⁻¹) * (b : D)⁻¹ := by group
        _ = ((b : D) * x * (b : D)⁻¹)⁻¹ := by rw [hsx]; group
    rw [hbs]
    rcases hconj b (Subgroup.mem_inf.mp b.2).1 with h1 | h1
    · rw [h1]
      exact Or.inr ⟨rfl, hxx⟩
    · rw [h1, inv_inv]
      exact Or.inl ⟨rfl, hxx⟩
  have hC4 : Nat.card C = 4 := by
    have h1 := (C.subgroupOf T).card_mul_index
    rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : C ≤ T)).toEquiv,
      hT8, ← hC] at h1
    omega
  have hCcyc : IsCyclic ↥C := by
    by_contra hnc
    have hCK : IsKleinFour ↥C := isKleinFour_of_card_four hC4 hnc
    refine hT.false_of_kleinFour_commute eK (inf_le_left.trans inf_le_right) hC4
      (fun v hv => by simpa using congrArg Subtype.val (IsKleinFour.mul_self (⟨v, hv⟩ : ↥C)))
      (hT.le_left hxL) hxo fun v hv => ?_
    exact (commute_iff_conj_eq).mpr ((hmemC v hv.1).mp hv)
  obtain ⟨g, hg⟩ := hCcyc.exists_generator
  set c : D := (g : D) with hcdef
  have hco : orderOf c = 4 := by
    rw [hcdef, Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hC4]
  have hcC : c ∈ C := g.2
  have hcT : c ∈ T := hcC.1
  have hcx : x * c = c * x := ((commute_iff_conj_eq).mpr ((hmemC c hcT).mp hcC)).symm
  have hzC : Subgroup.zpowers c ≤ C := Subgroup.zpowers_le.mpr hcC
  have hsC : s ∉ C := fun h1 => hxx (hsx ▸ (hmemC s hsT).mp h1)
  have hrel : s ^ 2 = 1 ∧ s * c * s⁻¹ = c⁻¹ := by
    have hne : ∀ k : ℕ, (⟨s, hsT⟩ : ↥T) ≠ ⟨c, hcT⟩ ^ k := fun k h1 => hsC (hzC (by
      have := congrArg Subtype.val h1
      simp only [SubmonoidClass.mk_pow] at this
      rw [this]
      exact Subgroup.npow_mem_zpowers c k))
    have ha : eT ⟨c, hcT⟩ ^ 2 ≠ 1 := by
      intro h1
      rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
      have h2 : c ^ 2 = 1 := by simpa using congrArg Subtype.val h1
      have := orderOf_dvd_of_pow_eq_one h2
      rw [hco] at this
      norm_num at this
    have key := dihedral_four_outside (eT ⟨c, hcT⟩) (eT ⟨s, hsT⟩) ha
      (fun h1 => hne 0 (eT.injective (by rw [h1, pow_zero, map_one])))
      (fun h1 => hne 1 (eT.injective (by rw [h1, pow_one])))
      (fun h1 => hne 2 (eT.injective (by rw [h1, map_pow])))
      (fun h1 => hne 3 (eT.injective (by rw [h1, map_pow])))
    obtain ⟨k1, k2⟩ := key
    rw [← map_pow, MulEquiv.map_eq_one_iff] at k1
    rw [← map_inv, ← map_mul, ← map_inv, ← map_mul] at k2
    refine ⟨by simpa using congrArg Subtype.val k1, ?_⟩
    have := congrArg Subtype.val (eT.injective k2)
    simpa using this
  set r := x * c with hr
  have hro : orderOf r = 12 := by
    rw [hr, Commute.orderOf_mul_eq_mul_orderOf_of_coprime hcx (by rw [hxo, hco]; norm_num),
      hxo, hco]
  have hsr : s * r * s⁻¹ = r⁻¹ := by
    calc s * r * s⁻¹ = (s * x * s⁻¹) * (s * c * s⁻¹) := by rw [hr]; group
      _ = x⁻¹ * c⁻¹ := by rw [hsx, hrel.2]
      _ = (c * x)⁻¹ := by group
      _ = r⁻¹ := by rw [hr, ← hcx]
  have hsr' : s ∉ Subgroup.zpowers r := by
    intro h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply hxx
    rw [← hsx]
    have hrx : Commute r x :=
      (Commute.refl x).mul_left (show Commute c x from (show Commute x c from hcx).symm)
    rw [(hrx.zpow_left k).eq, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨e⟩ := nonempty_dihedral_of_inverting hrel.1 hsr hsr'
  rw [hro] at e
  have hle : Subgroup.zpowers r ⊔ Subgroup.zpowers s ≤ G₁ := by
    refine sup_le (Subgroup.zpowers_le.mpr ?_)
      (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hsT).1)
    exact G₁.mul_mem hxG (Subgroup.mem_inf.mp hcT).1
  have heq : Subgroup.zpowers r ⊔ Subgroup.zpowers s = G₁ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_left h, hT8, Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  exact ⟨(MulEquiv.subgroupCongr heq).symm.trans e⟩


theorem mem_pCoreOf_of_commute
    (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F) {g : D}
    (hg : g ∈ G₂) (hc : ∀ q ∈ pCoreOf 2 G₂, g * q = q * g) : g ∈ pCoreOf 2 G₂ :=
  (hT.mem_inf_of_commute eK hg fun v hv => hc v hv.1).1

theorem mem_of_card_eq_four {Q : Subgroup D} (hQ : Nat.card ↥Q = 4) {u v y : D} (hu : u ∈ Q)
    (hv : v ∈ Q) (hy : y ∈ Q) (hv1 : v ≠ 1) (hu1 : u ≠ 1) (huv : u ≠ v) (hv2 : v * v = 1) :
    y = 1 ∨ y = v ∨ y = u ∨ y = u * v := by
  classical
  have : Fintype ↥(Q : Set D) := Fintype.ofFinite _
  by_contra hne
  push Not at hne
  obtain ⟨hy1, hyv, hyu, hyuv⟩ := hne
  have huv1 : u * v ≠ 1 := fun h1 => huv (by
    calc u = u * v * v := by rw [mul_assoc, hv2, mul_one]
      _ = v := by rw [h1, one_mul])
  have huvv : u * v ≠ v := fun h1 => hu1 (by
    calc u = u * v * v⁻¹ := by group
      _ = 1 := by rw [h1, mul_inv_cancel])
  have huvu : u * v ≠ u := fun h1 => hv1 (by
    calc v = u⁻¹ * (u * v) := by group
      _ = 1 := by rw [h1, inv_mul_cancel])
  have hsub : ({1, v, u, u * v, y} : Finset D) ⊆ (Q : Set D).toFinset := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    simp only [Set.mem_toFinset, SetLike.mem_coe]
    rcases hz with rfl | rfl | rfl | rfl | rfl
    · exact Q.one_mem
    · exact hv
    · exact hu
    · exact Q.mul_mem hu hv
    · exact hy
  have hcard : ({1, v, u, u * v, y} : Finset D).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hv1.symm, hu1.symm, huv1.symm, hy1.symm]),
      Finset.card_insert_of_notMem (by simp [huv.symm, huvv.symm, hyv.symm]),
      Finset.card_insert_of_notMem (by simp [huvu.symm, hyu.symm]),
      Finset.card_pair (Ne.symm hyuv)]
  have hQc : (Q : Set D).toFinset.card = 4 := by
    rw [← Nat.card_eq_card_toFinset, ← hQ]
    rfl
  have := Finset.card_le_card hsub
  omega

theorem nonempty_right_mulEquiv_perm
    (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F) :
    Nonempty (↥G₂ ≃* Equiv.Perm (Fin 4)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hT.triple
  obtain ⟨-, hQ4, hT8⟩ := hT.inf_inf_eq eK
  set Q₂ := pCoreOf 2 G₂ with hQ₂
  have hEA := hT.elemAbelian.1
  have hcommQ : ∀ a ∈ Q₂, ∀ b ∈ Q₂, a * b = b * a := fun a ha b hb =>
    congrArg (Subtype.val : ↥Q₂ → D) (hEA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  obtain ⟨w, hwG, hwo⟩ := exists_orderOf_eq_three_left h.symm
  have hw3 : w ^ 3 = 1 := hwo ▸ pow_orderOf_eq_one w
  have hwN : w ∈ Subgroup.normalizer (Q₂ : Set D) := le_normalizer_pCoreOf 2 G₂ hwG
  have hconjQ : ∀ q ∈ Q₂, w * q * w⁻¹ ∈ Q₂ := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp hwN q).mp hq
  have hwQ : ¬ ∀ q ∈ Q₂, w * q = q * w := by
    intro hall
    have hwQ' := hT.mem_pCoreOf_of_commute eK hwG hall
    obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 G₂) ⟨w, hwQ'⟩
    have hk' : w ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := Nat.eq_one_of_dvd_coprimes (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hw3)
    rw [hwo] at h1
    norm_num at h1
  have hfpf : ∀ v ∈ Q₂, v ≠ 1 → w * v * w⁻¹ ≠ v := by
    intro v hv hv1 hfix
    apply hwQ
    have hv2 : v * v = 1 := by rw [← pow_two]; exact hEA.2 v hv
    obtain ⟨u, hu, hu1, huv⟩ : ∃ u ∈ Q₂, u ≠ 1 ∧ u ≠ v := by
      by_contra hne
      push Not at hne
      have hle : Q₂ ≤ Subgroup.zpowers v := fun y hy => by
        by_cases hy1 : y = 1
        · rw [hy1]; exact Subgroup.one_mem _
        · rw [hne y hy hy1]; exact Subgroup.mem_zpowers v
      have h2 : Nat.card ↥(Subgroup.zpowers v) ≤ 2 := by
        rw [Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one (by norm_num) (by rw [pow_two]; exact hv2)
      have := Subgroup.card_le_of_le hle
      omega
    have henum : ∀ y ∈ Q₂, y = 1 ∨ y = v ∨ y = u ∨ y = u * v := fun y hy =>
      mem_of_card_eq_four hQ4 hu hv hy hv1 hu1 huv hv2
    have hwu : w * u * w⁻¹ = u := by
      rcases henum _ (hconjQ u hu) with h1 | h1 | h1 | h1
      · exfalso
        apply hu1
        calc u = w⁻¹ * (w * u * w⁻¹) * w := by group
          _ = 1 := by rw [h1]; group
      · exfalso
        apply huv
        calc u = w⁻¹ * (w * u * w⁻¹) * w := by group
          _ = w⁻¹ * (w * v * w⁻¹) * w := by rw [h1, hfix]
          _ = v := by group
      · exact h1
      · exfalso
        have e2 : w * (w * u * w⁻¹) * w⁻¹ = u := by
          calc w * (w * u * w⁻¹) * w⁻¹ = w * (u * v) * w⁻¹ := by rw [h1]
            _ = (w * u * w⁻¹) * (w * v * w⁻¹) := by group
            _ = u * v * v := by rw [h1, hfix]
            _ = u := by rw [mul_assoc, hv2, mul_one]
        have e3 : u = u * v := by
          have hw3' : w * w * w = 1 := by rw [← hw3, pow_three, mul_assoc]
          calc u = (w * w * w) * u * (w * w * w)⁻¹ := by rw [hw3', one_mul, inv_one, mul_one]
            _ = w * (w * (w * u * w⁻¹) * w⁻¹) * w⁻¹ := by group
            _ = w * u * w⁻¹ := by rw [e2]
            _ = u * v := h1
        apply hv1
        calc v = u⁻¹ * (u * v) := by group
          _ = 1 := by rw [← e3, inv_mul_cancel]
    intro y hy
    have hcv : w * v = v * w := (commute_iff_conj_eq).mpr hfix
    have hcu : w * u = u * w := (commute_iff_conj_eq).mpr hwu
    rcases henum y hy with rfl | rfl | rfl | rfl
    · simp
    · exact hcv
    · exact hcu
    · calc w * (u * v) = (w * u) * v := by group
        _ = u * (w * v) := by rw [hcu]; group
        _ = u * v * w := by rw [hcv]; group
  set X := Q₂ ⊔ Subgroup.zpowers w with hX
  have hQw : Q₂ ⊓ Subgroup.zpowers w = ⊥ := by
    have h1 : Nat.card ↥(Q₂ ⊓ Subgroup.zpowers w) ∣ 4 := hQ4 ▸ Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(Q₂ ⊓ Subgroup.zpowers w) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : Q₂ ⊓ Subgroup.zpowers w ≤ _)
      rwa [Nat.card_zpowers, hwo] at this
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes (by norm_num) h1 h2)
  have hX12 : Nat.card ↥X = 12 := by
    have hzN : Subgroup.zpowers w ≤ Subgroup.normalizer (Q₂ : Set D) :=
      Subgroup.zpowers_le.mpr hwN
    have h1 := A4.relIndex_sup_eq_of_le_normalizer' (D := Q₂) (T := Subgroup.zpowers w) hzN
    have h2 := Subgroup.relIndex_mul_card (H := Q₂) (K := Subgroup.zpowers w ⊔ Q₂)
    have h3 := Subgroup.relIndex_mul_card (H := Q₂) (K := Subgroup.zpowers w)
    rw [inf_eq_left.mpr le_sup_right, h1] at h2
    rw [hQw, Subgroup.card_bot, mul_one, Nat.card_zpowers, hwo] at h3
    rw [hX, sup_comm, ← h2, h3, hQ4]
  have hcen : ∀ g ∈ G₂, (∀ l ∈ X, g * l = l * g) → g = 1 := by
    intro g hg hgl
    have hgQ := hT.mem_pCoreOf_of_commute eK hg fun q hq => hgl q ((le_sup_left : Q₂ ≤ X) hq)
    by_contra hg1
    apply hfpf g hgQ hg1
    have := hgl w ((le_sup_right : Subgroup.zpowers w ≤ X) (Subgroup.mem_zpowers w))
    rw [← this, mul_assoc, mul_inv_cancel, mul_one]
  have hXG : X ≤ G₂ := sup_le (pCoreOf_le 2 G₂) (Subgroup.zpowers_le.mpr hwG)
  have hA4 : S14110.A4Data X Q₂ w :=
    { le := le_sup_left
      card_W := hQ4
      sq_eq_one := hEA.2
      comm := hcommQ
      mem_X := (le_sup_right : Subgroup.zpowers w ≤ X) (Subgroup.mem_zpowers w)
      order_c := hwo
      mem_normalizer := hwN
      fpf := hfpf
      eq_sup := rfl
      card_X := hX12
      center := fun g hg hgl => hcen g (hXG hg) hgl }
  have hG24 : Nat.card ↥G₂ = 24 := by rw [card_right h, hT8]
  have hidx : X.relIndex G₂ = 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := X) (K := G₂)
    rw [inf_eq_left.mpr hXG, hX12, hG24] at h1
    omega
  have hXn : (X.subgroupOf G₂).Normal := Subgroup.normal_of_index_eq_two hidx
  have hnorm : ∀ g ∈ G₂, g ∈ Subgroup.normalizer (X : Set D) := fun g hg =>
    mem_normalizer_of_forall_conj_mem fun x hx => by
      have := hXn.conj_mem ⟨x, hXG hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
      simpa [Subgroup.mem_subgroupOf] using this
  have hne : ∃ g ∈ G₂, g ∉ X := by
    by_contra hall
    push Not at hall
    have := Subgroup.card_le_of_le (show G₂ ≤ X from hall)
    omega
  exact S14110.nonempty_mulEquiv_perm_four hA4 hXG hnorm hcen hne


theorem mod_twentyfour
    (hT : F617L2 G₁ G₂ K F p) (eK : ↥K ≃* PSL2 F) :
    p % 24 = 11 ∨ p % 24 = 13 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hQ4, -⟩ := hT.inf_inf_eq eK
  have hQK := hT.pCoreOf_le_component eK
  set Q₂ := pCoreOf 2 G₂ with hQ₂
  have hEA := hT.elemAbelian.1
  have hsqQ : ∀ q ∈ Q₂, q * q = 1 := fun q hq => by rw [← pow_two]; exact hEA.2 q hq
  obtain ⟨x, hxL, hxo, -, hxn⟩ := hT.exists_generator
  have hxK : x ∈ K := hT.le_left hxL
  have hxx : x⁻¹ ≠ x := by
    intro h1
    have h2 : x ^ 2 = 1 := by rw [pow_two]; nth_rewrite 1 [← h1]; exact inv_mul_cancel x
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hxo] at this
    norm_num at this
  obtain ⟨z, hzQ, hz1, hzx⟩ := F617Setting.exists_ne_one_commute hEA (by rw [hQ4]) hxn
  obtain ⟨s, hsQ, hsx⟩ : ∃ s ∈ Q₂, s * x * s⁻¹ = x⁻¹ := by
    by_contra hne
    push Not at hne
    refine hT.false_of_kleinFour_commute eK (pCoreOf_le 2 G₂) hQ4 hsqQ hxK hxo fun v hv => ?_
    rcases hxn v hv with h1 | h1
    · exact (commute_iff_conj_eq).mpr h1
    · exact absurd h1 (hne v hv)
  have hzo : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hsqQ z hzQ) hz1
  set r := x * z with hr
  have hro : orderOf r = 6 := by
    rw [hr, Commute.orderOf_mul_eq_mul_orderOf_of_coprime (show Commute x z from hzx.symm)
      (by rw [hxo, hzo]; norm_num), hxo, hzo]
  have hsz : s * z * s⁻¹ = z := by
    rw [hEA.1.is_comm.comm ⟨s, hsQ⟩ ⟨z, hzQ⟩ |> congrArg (Subtype.val : ↥Q₂ → D) |>
      fun h => show s * z = z * s from h, mul_assoc, mul_inv_cancel, mul_one]
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_left (hsqQ z hzQ)
  have hsr : s * r * s⁻¹ = r⁻¹ := by
    calc s * r * s⁻¹ = (s * x * s⁻¹) * (s * z * s⁻¹) := by rw [hr]; group
      _ = x⁻¹ * z := by rw [hsx, hsz]
      _ = z⁻¹ * x⁻¹ := by
        rw [hzinv]
        calc x⁻¹ * z = x⁻¹ * (z * x) * x⁻¹ := by group
          _ = x⁻¹ * (x * z) * x⁻¹ := by rw [hzx]
          _ = z * x⁻¹ := by group
      _ = r⁻¹ := by rw [hr, mul_inv_rev]
  have hs2 : s ^ 2 = 1 := by rw [pow_two]; exact hsqQ s hsQ
  have hsr' : s ∉ Subgroup.zpowers r := by
    intro h1
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply hxx
    rw [← hsx]
    have hrx : Commute r x := (Commute.refl x).mul_left hzx
    rw [(hrx.zpow_left k).eq, mul_assoc, mul_inv_cancel, mul_one]
  have hsK : s ∈ K := hQK hsQ
  have hrK : r ∈ K := K.mul_mem hxK (hQK hzQ)
  set eS : ↥K ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F) :=
    eK.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F) with heS
  have : Finite (Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F)) :=
    Finite.of_equiv _ eS.toEquiv
  set r' := eS ⟨r, hrK⟩ with hr'
  set s' := eS ⟨s, hsK⟩ with hs'
  have hr'o : orderOf r' = 6 := by rw [hr', MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hro]
  have hs'2 : s' ^ 2 = 1 := by
    rw [hs', ← map_pow, MulEquiv.map_eq_one_iff]
    exact Subtype.ext (by simpa using hs2)
  have hs'r' : s' * r' * s'⁻¹ = r'⁻¹ := by
    rw [hs', hr', ← map_inv, ← map_mul, ← map_mul, ← map_inv]
    congr 1
    exact Subtype.ext (by simpa using hsr)
  have hs'z : s' ∉ Subgroup.zpowers r' := by
    intro h1
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    apply hsr'
    rw [hr', hs', ← map_zpow] at hk
    have := congrArg Subtype.val (eS.injective hk)
    simp only [SubgroupClass.coe_zpow] at this
    rw [← this]
    exact Subgroup.zpow_mem_zpowers r k
  obtain ⟨e⟩ := nonempty_dihedral_of_inverting hs'2 hs'r' hs'z
  rw [hr'o] at e
  have hp2 : p ≠ 2 := by have := hT.five_le; omega
  obtain ⟨h12, -, -⟩ := l2DicksonFacts_holds p 1 F hT.prime hp2 le_rfl
    (by rw [hT.card_field, pow_one]) (Subgroup.zpowers r' ⊔ Subgroup.zpowers s')
  have h12' := h12 ⟨e⟩
  rw [pow_one] at h12'
  have h8 := hT.mod_eight
  omega

end F617L2

namespace F617Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D}

theorem isF618CaseThree
    (hS : F617Setting G₁ G₂ K) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hp8 : p % 8 = 3 ∨ p % 8 = 5) {F : Type} [Field F] [Finite F] (hF : Nat.card F = p)
    (hL2 : IsL2 p 1 ↥K)
    (eK : ↥K ≃* Assembly.LowTwoRank.StatedProj (Assembly.LowTwoRank.StatedSL 2 F)) :
    IsF618CaseThree G₁ G₂ := by
  have hT : F617L2 G₁ G₂ K F p := ⟨hS, hp, hp5, hp8, hF⟩
  set eK' : ↥K ≃* PSL2 F :=
    eK.trans (Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm
  exact ⟨p, K, Subgroup.centralizer (K : Set D), hp, hT.mod_twentyfour eK', hL2,
    hT.card_centralizer eK', hT.sup_centralizer eK', F617L2.inf_centralizer_self_eq_bot eK',
    fun k hk z hz => Subgroup.mem_centralizer_iff.mp hz k hk,
    hT.nonempty_inf_mulEquiv_dihedral eK', hT.nonempty_left_mulEquiv_dihedral eK',
    hT.nonempty_right_mulEquiv_perm eK', fun t ht htK => hT.inducesOuterAut eK' ht htK⟩

end F617Setting

end F6

end CFSG.Quasithin
