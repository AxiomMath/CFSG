module

public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PSubgroupInfNormalNilpotentLePCore

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS18

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (projectiveSL)

variable {Y : Type} [Group Y]

theorem eq_of_mul_inv_mem_center {L : Type} [Group L] (hL : commutator L = ⊤) (σ : MulAut L)
    (hσ : ∀ l : L, σ l * l⁻¹ ∈ Subgroup.center L) (l : L) : σ l = l := by
  let f : L →* Subgroup.center L :=
    { toFun := fun l => ⟨σ l * l⁻¹, hσ l⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        change σ (a * b) * (a * b)⁻¹ = σ a * a⁻¹ * (σ b * b⁻¹)
        have hb := Subgroup.mem_center_iff.mp (hσ b) (σ a)
        rw [map_mul, mul_inv_rev]
        calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * (σ b * b⁻¹) * a⁻¹ := by group
          _ = (σ b * b⁻¹) * σ a * a⁻¹ := by rw [← hb]
          _ = σ a * a⁻¹ * (σ b * b⁻¹) := by
            have ha := Subgroup.mem_center_iff.mp (hσ b) (σ a * a⁻¹)
            rw [mul_assoc, ← ha]) }
  have hker : commutator L ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [hL] at hker
  have h1 : f l = 1 := hker (Subgroup.mem_top l)
  have h2 : σ l * l⁻¹ = 1 := congrArg Subtype.val h1
  rwa [mul_inv_eq_one] at h2

@[expose] noncomputable def actOn (L : Subgroup Y) [L.Normal] {P : Type} [Group P]
    (ψ : L ⧸ Subgroup.center L ≃* P) : Y →* MulAut P :=
  (MulAut.congr ψ).toMonoidHom.comp ((centerDescend L).comp MulAut.conjNormal)

theorem actOn_apply (L : Subgroup Y) [L.Normal] {P : Type} [Group P]
    (ψ : L ⧸ Subgroup.center L ≃* P) (y : Y) (l : L) :
    actOn L ψ y (ψ (l : L ⧸ Subgroup.center L)) =
      ψ ((MulAut.conjNormal y l : L) : L ⧸ Subgroup.center L) := by
  simp [actOn, MulAut.congr_apply, centerDescend_mk]

theorem mem_centralizer_of_actOn_eq_one {L : Subgroup Y} [L.Normal] (hL : commutator L = ⊤)
    {P : Type} [Group P] (ψ : L ⧸ Subgroup.center L ≃* P) {y : Y} (hy : actOn L ψ y = 1) :
    y ∈ Subgroup.centralizer (L : Set Y) := by
  have h1 : ∀ l : L, MulAut.conjNormal y l * l⁻¹ ∈ Subgroup.center L := by
    intro l
    have := congrArg (fun α : MulAut P => α (ψ (l : L ⧸ Subgroup.center L))) hy
    simp only [actOn_apply, MulAut.one_apply] at this
    have h2 := ψ.injective this
    rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv] at h2
    exact h2
  have h3 := eq_of_mul_inv_mem_center hL _ h1
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have := congrArg Subtype.val (h3 ⟨l, hl⟩)
  rw [MulAut.conjNormal_apply] at this
  calc l * y = y * l * y⁻¹ * y := by rw [this]
    _ = y * l := by group

theorem eq_bot_of_le_centralizer_of_nilpotent [Finite Y] (hO : CFSG.pCore 2 Y = ⊥)
    {X : Subgroup Y} [X.Normal] (hab : ∀ a b : Y ⧸ X, a * b = b * a) {R : Subgroup Y}
    (hR : IsPGroup 2 R) (hRX : R ≤ Subgroup.centralizer (X : Set Y)) : R = ⊥ := by
  set S := Subgroup.centralizer (X : Set Y) with hSdef
  have hSn : S.Normal := Subgroup.normal_centralizer
  let f : S →* Y ⧸ X := (QuotientGroup.mk' X).comp S.subtype
  have hker : f.ker ≤ Subgroup.center S := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have hsX : (s : Y) ∈ X := (QuotientGroup.eq_one_iff _).mp hs
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp g.2 _ hsX).symm
  let _ : CommGroup (Y ⧸ X) := { mul_comm := hab }
  have hnil : Group.IsNilpotent S := Subgroup.isNilpotent_of_ker_le_center f hker
  have hle := CFSG.GorensteinWalter.pSubgroup_inf_normal_nilpotent_le_pCore R S 2
    Nat.prime_two hR hSn hnil
  rw [inf_eq_left.mpr hRX, hO] at hle
  exact le_bot_iff.mp hle

variable {k : Type} [Field k]

theorem outer_involution_of_act [Finite Y] (hk : Nat.card k = 4) {X L E : Subgroup Y} {t : Y}
    [L.Normal] (hX : X.Normal) (hLperf : commutator L = ⊤)
    (ψ : L ⧸ Subgroup.center L ≃* projectiveSL 3 k)
    (hE9 : ∃ E9 : Subgroup (projectiveSL 3 k), Nat.card E9 = 9 ∧
      ∀ g ∈ E9, ∃ e ∈ E, actOn L ψ e = MulAut.conj g)
    (hEX : E ≤ X) (hCX : IsPGroup 3 ↥(X ⊓ Subgroup.centralizer (L : Set Y)))
    (hKL : ∀ R : Subgroup Y, IsPGroup 2 R → R ≤ Subgroup.centralizer (L : Set Y) →
      R ≤ Subgroup.centralizer (E : Set Y) → R = ⊥)
    (htX : t ∉ X) (ht2 : IsPGroup 2 (Subgroup.zpowers t))
    (hEt : E ≤ Subgroup.centralizer ({t} : Set Y)) :
    t ^ 2 = 1 ∧ ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t := by
  set ρ := actOn L ψ with hρ
  obtain ⟨E9, hE9c, hE9⟩ := hE9
  have hCLn : (Subgroup.centralizer (L : Set Y)).Normal := Subgroup.normal_centralizer
  have htE : Subgroup.zpowers t ≤ Subgroup.centralizer (E : Set Y) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro e he
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEt he)
  have hρt : ρ t ≠ 1 := by
    intro h
    have htL := mem_centralizer_of_actOn_eq_one hLperf ψ h
    have := hKL _ ht2 (Subgroup.zpowers_le.mpr htL) htE
    rw [Subgroup.zpowers_eq_bot] at this
    exact htX (this ▸ X.one_mem)
  have key : ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      Nat.card T = 2 := by
    intro T hT hET htT
    have hR : T ⊓ Subgroup.centralizer (L : Set Y) = ⊥ := by
      refine hKL _ (hT.to_inf_left) inf_le_right ?_
      rw [Subgroup.le_centralizer_iff]
      intro e he r hr
      have h1 : e * r * e⁻¹ * r⁻¹ ∈ T := by
        refine T.mul_mem ?_ (T.inv_mem hr.1)
        exact (Subgroup.mem_normalizer_iff.mp (hET he) r).mp hr.1
      have h2 : e * r * e⁻¹ * r⁻¹ ∈ Subgroup.centralizer (L : Set Y) := by
        refine Subgroup.mul_mem _ ?_ (Subgroup.inv_mem _ hr.2)
        exact hCLn.conj_mem r hr.2 e
      have h3 : e * r * e⁻¹ * r⁻¹ ∈ X := by
        have h5 : e * (r * e⁻¹ * r⁻¹) ∈ X :=
          X.mul_mem (hEX he) (hX.conj_mem _ (X.inv_mem (hEX he)) r)
        simpa only [mul_assoc] using h5
      have h4 : e * r * e⁻¹ * r⁻¹ = 1 := by
        obtain ⟨m, hm⟩ := hT ⟨_, h1⟩
        obtain ⟨n, hn⟩ := hCX ⟨_, ⟨h3, h2⟩⟩
        have hm' : (e * r * e⁻¹ * r⁻¹) ^ 2 ^ m = 1 := congrArg Subtype.val hm
        have hn' : (e * r * e⁻¹ * r⁻¹) ^ 3 ^ n = 1 := congrArg Subtype.val hn
        have hd : orderOf (e * r * e⁻¹ * r⁻¹) ∣ Nat.gcd (2 ^ m) (3 ^ n) :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hm') (orderOf_dvd_of_pow_eq_one hn')
        rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow m n (by norm_num))] at hd
        exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
      calc r * e = e * r * e⁻¹ * r⁻¹ * (r * e) := by rw [h4, one_mul]
        _ = e * r := by group
    have hinj : Function.Injective (ρ.domRestrict T) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hxL := mem_centralizer_of_actOn_eq_one hLperf ψ hx
      have : (x : Y) ∈ T ⊓ Subgroup.centralizer (L : Set Y) := ⟨x.2, hxL⟩
      rw [hR, Subgroup.mem_bot] at this
      exact Subtype.ext this
    have : Finite (T.map ρ) := Finite.of_surjective (ρ.subgroupMap T) (ρ.subgroupMap_surjective T)
    have hTρ2 : IsPGroup 2 (T.map ρ) := hT.map ρ
    have hnot3 : ¬ 3 ∣ Nat.card (T.map ρ) := by
      obtain ⟨n, hn⟩ := hTρ2.exists_card_eq
      rw [hn]
      intro h
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
      norm_num at this
    have hnormE : ∀ g ∈ E9, MulAut.conj g ∈
        Subgroup.normalizer ((T.map ρ : Subgroup (MulAut (projectiveSL 3 k))) :
          Set (MulAut (projectiveSL 3 k))) := by
      intro g hg
      obtain ⟨e, he, hρe⟩ := hE9 g hg
      rw [← hρe]
      refine Subgroup.mem_normalizer_fintype fun x hx => ?_
      obtain ⟨y, hy, rfl⟩ := hx
      refine ⟨e * y * e⁻¹, (Subgroup.mem_normalizer_iff.mp (hET he) y).mp hy, ?_⟩
      rw [map_mul, map_mul, map_inv]
    rcases L34.eq_bot_or_eq_zpowers_graphField hk hE9c hnot3 hnormE with hbot | ⟨τ, hτ, hτ1, hτ2, -⟩
    · exfalso
      have : ρ t ∈ T.map ρ := ⟨t, htT, rfl⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hρt this
    · have hcardρ : Nat.card (T.map ρ) = 2 := by
        rw [hτ, Nat.card_zpowers]
        exact orderOf_eq_prime (by rw [sq]; exact hτ2) hτ1
      have h1 : Nat.card T = Nat.card (T.map ρ) := by
        rw [← MonoidHom.domRestrict_range]
        exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
      rw [h1, hcardρ]
  have hTt : ∀ T : Subgroup Y, IsPGroup 2 T → E ≤ Subgroup.normalizer (T : Set Y) → t ∈ T →
      T = Subgroup.zpowers t := by
    intro T hT hET htT
    have h2 := key T hT hET htT
    have hle : Subgroup.zpowers t ≤ T := Subgroup.zpowers_le.mpr htT
    have ht1 : t ≠ 1 := fun h => htX (h ▸ X.one_mem)
    have hz : 2 ≤ Nat.card (Subgroup.zpowers t) := by
      rw [Nat.card_zpowers]
      have hpos := orderOf_pos t
      have hne : orderOf t ≠ 1 := fun h => ht1 (orderOf_eq_one_iff.mp h)
      omega
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [h2]; exact hz)).symm
  have hEz : E ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup Y) : Set Y) := by
    intro e he
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    have hc : n * e = e * n := (Subgroup.mem_centralizer_iff.mp (htE hn) e he).symm
    rw [← hc, mul_inv_cancel_right]
    exact hn
  refine ⟨?_, hTt⟩
  have h2 := key (Subgroup.zpowers t) ht2 hEz (Subgroup.mem_zpowers t)
  rw [Nat.card_zpowers] at h2
  rw [← h2]
  exact pow_orderOf_eq_one t

end CFSG.RankThree.PartTwo.KFacts.KS18
