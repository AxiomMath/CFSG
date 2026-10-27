module

public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.D2Offenders
public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.InvolutionQuadratic
public import CFSG.Quasithin.Background.OddCoprimeFixV

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup

variable {V : Type*} [CommGroup V]

private theorem mul_eq_mul_inv_of_invert {G : Type*} [Group G] {t τ : G} (ht : t ^ 2 = 1)
    (h : t * τ * t⁻¹ = τ⁻¹) : τ * t = t * τ⁻¹ := by
  have htt : t * t = 1 := by rw [← pow_two]; exact ht
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have h1 : t * τ * t = τ⁻¹ := by simpa only [htinv] using h
  calc τ * t = (t * t) * τ * t := by rw [htt, one_mul]
    _ = t * (t * τ * t) := by group
    _ = t * τ⁻¹ := by rw [h1]

theorem mem_commV_of_fixed [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t τ : MulAut V}
    (ht : t ^ 2 = 1) (hτ : Odd (orderOf τ)) (htτ : t * τ * t⁻¹ = τ⁻¹) {W : Subgroup V}
    (hWt : ∀ w ∈ W, t w ∈ W) (hWτ : ∀ w ∈ W, τ w ∈ W) (hfree : ∀ w ∈ W, τ w = w → w = 1)
    {w : V} (hw : w ∈ W) (htw : t w = w) : ∃ x ∈ W, w = t x * x⁻¹ := by
  classical
  have hinv : ∀ v : V, v⁻¹ = v :=
    fun v => inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV v)
  let φ : W →* W :=
    { toFun := fun x => ⟨t x.1 * x.1⁻¹, W.mul_mem (hWt x.1 x.2) (W.inv_mem x.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        show t (a.1 * b.1) * (a.1 * b.1)⁻¹ = t a.1 * a.1⁻¹ * (t b.1 * b.1⁻¹)
        rw [map_mul, mul_inv_rev]
        ac_rfl }
  have hker : ∀ x : W, x ∈ φ.ker ↔ t x.1 = x.1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h1 : t x.1 * x.1⁻¹ = 1 := congrArg (fun y : W => y.1) h
      rwa [mul_inv_eq_one] at h1
    · intro h
      apply Subtype.ext
      show t x.1 * x.1⁻¹ = 1
      rw [mul_inv_eq_one]
      exact h
  have hrange : φ.range ≤ φ.ker := by
    rintro y ⟨x, rfl⟩
    rw [hker]
    show t (t x.1 * x.1⁻¹) = t x.1 * x.1⁻¹
    have h2 : t (t x.1) = x.1 := by
      have h := congrArg (fun g : MulAut V => g x.1) ht
      simpa [pow_two, MulAut.mul_apply] using h
    rw [map_mul, map_inv, h2, hinv (t x.1), hinv x.1]
    exact mul_comm _ _
  have hcard := Subgroup.card_ker_mul_card_range φ
  set A : Subgroup V := φ.ker.map W.subtype with hA
  have hAcard : Nat.card A = Nat.card φ.ker :=
    Subgroup.card_map_of_injective W.subtype_injective
  have hAle : A ≤ W := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hAτle : A.map τ.toMonoidHom ≤ W := by
    rintro _ ⟨a, ha, rfl⟩
    exact hWτ a (hAle ha)
  have hinf : A ⊓ A.map τ.toMonoidHom = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvA, hvAτ⟩
    obtain ⟨x, hxK, hxv⟩ := Subgroup.mem_map.mp hvA
    obtain ⟨a, haA, hav⟩ := Subgroup.mem_map.mp hvAτ
    obtain ⟨b, hbK, hba⟩ := Subgroup.mem_map.mp haA
    have htx : t (W.subtype x) = W.subtype x := (hker x).mp hxK
    have hta : t a = a := by
      have hb : t (W.subtype b) = W.subtype b := (hker b).mp hbK
      rw [← hba, hb]
    have haeq : τ a = W.subtype x := hav.trans hxv.symm
    have h1 : t (τ a) = W.subtype x := (congrArg (fun v : V => t v) haeq).trans htx
    have hτt : τ * t = t * τ⁻¹ := mul_eq_mul_inv_of_invert ht htτ
    have htτ' : t * τ = τ⁻¹ * t := by
      calc t * τ = (t * τ * t⁻¹) * t := by group
        _ = τ⁻¹ * t := by rw [htτ]
    have h2 : t (τ a) = τ⁻¹ a := by
      have h := congrArg (fun f : MulAut V => f a) htτ'
      rw [MulAut.mul_apply, MulAut.mul_apply, hta] at h
      exact h
    have h3 : τ a = τ⁻¹ a := haeq.trans (h1.symm.trans h2)
    have h4 : τ (τ a) = a := by
      have h := congrArg (fun v : V => τ v) h3
      rwa [MulAut.apply_inv_self] at h
    have hτodd : Nat.Coprime 2 (orderOf τ) := Nat.coprime_two_left.mpr hτ
    have hzp : Subgroup.zpowers (τ ^ 2) = Subgroup.zpowers τ := by
      refine le_antisymm (Subgroup.zpowers_le.mpr (Subgroup.npow_mem_zpowers τ 2)) ?_
      rw [Subgroup.zpowers_le]
      exact mem_zpowers_pow_iff.mpr hτodd
    have hafix : a ∈ fixV (Subgroup.zpowers τ) := by
      rw [← hzp]
      exact mem_fixV_zpowers_iff.mpr (by simpa [pow_two, MulAut.mul_apply] using h4)
    have ha1 : a = 1 := hfree a (hAle haA) (mem_fixV_zpowers_iff.mp hafix)
    rw [Subgroup.mem_bot, ← hxv, ← haeq, ha1, map_one]
  have hAτcard : Nat.card (A.map τ.toMonoidHom) = Nat.card A :=
    Subgroup.card_map_of_injective τ.injective
  have hsq : Nat.card A * Nat.card A ≤ Nat.card W := by
    have h := CFSG.Quasithin.card_sup_mul_card_inf A (A.map τ.toMonoidHom)
    rw [hinf, Subgroup.card_bot, hAτcard, mul_one] at h
    rw [← h]
    exact Subgroup.card_le_of_le (sup_le hAle hAτle)
  have hkerle : Nat.card φ.ker * Nat.card φ.ker ≤ Nat.card W := by
    rw [← hAcard]
    exact hsq
  have hrangecard : Nat.card φ.range = Nat.card φ.ker := by
    have h2 : Nat.card φ.ker * Nat.card φ.ker ≤ Nat.card φ.ker * Nat.card φ.range := by
      rw [hcard]
      exact hkerle
    have h3 : Nat.card φ.ker ≤ Nat.card φ.range :=
      Nat.le_of_mul_le_mul_left h2 Nat.card_pos
    exact le_antisymm (Subgroup.card_le_of_le hrange) h3
  have heq : φ.range = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hrange (le_of_eq hrangecard.symm)
  have hwK : (⟨w, hw⟩ : W) ∈ φ.ker := by
    rw [hker]
    exact htw
  rw [← heq] at hwK
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hwK
  have hx' : (φ x).1 = w := congrArg (fun y : W => y.1) hx
  rw [show (φ x).1 = t x.1 * x.1⁻¹ from rfl] at hx'
  exact ⟨x.1, x.2, hx'.symm⟩

theorem commV_le_of_parrott [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {L Y : Subgroup (MulAut V)}
    (hfix : fixV L = ⊥) {t u τ : MulAut V} (ht : t ^ 2 = 1) (hu : u ^ 2 = 1)
    (htu : ∀ v : V, u (t v * v⁻¹) = t v * v⁻¹) (hut : ∀ v : V, t (u v * v⁻¹) = u v * v⁻¹)
    (hτ : Odd (orderOf τ)) (htτ : t * τ * t⁻¹ = τ⁻¹)
    (hY : ∀ y ∈ Y, ∀ w ∈ commV (zpowers t), y w = w)
    (hgen₁ : L ≤ Y ⊔ zpowers τ) (hgen₂ : L ≤ closure {t, u, τ}) :
    commV (zpowers u) ≤ commV (zpowers t) := by
  classical
  have hoddV : Odd (Nat.card (Subgroup.zpowers τ)) := by
    rw [Nat.card_zpowers]
    exact hτ
  have hτt : τ * t = t * τ⁻¹ := mul_eq_mul_inv_of_invert ht htτ
  have hτfixbot : commV (Subgroup.zpowers τ) ⊓ fixV (Subgroup.zpowers τ) = ⊥ :=
    commV_inf_fixV_eq_bot_of_odd_card hV _ hoddV
  have hu_fix : ∀ w ∈ commV (Subgroup.zpowers t), u w = w := by
    intro w hw
    have hle : commV (Subgroup.zpowers t) ≤ fixV (Subgroup.zpowers u) := by
      rw [commV, Subgroup.closure_le]
      rintro _ ⟨s, hs, x, rfl⟩
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      rcases CommVZ4.zpow_eq_one_or_self_of_sq ht n with h | h
      · rw [h]
        simp only [MulAut.one_apply, mul_inv_cancel]
        exact (fixV (Subgroup.zpowers u)).one_mem
      · rw [h]
        exact mem_fixV_zpowers_iff.mpr (htu x)
    exact (hle hw) u (Subgroup.mem_zpowers u)
  have hCa : ∀ c : V, τ c = c → t c = c := by
    intro c hc
    have hcF : c ∈ fixV (Subgroup.zpowers τ) := mem_fixV_zpowers_iff.mpr hc
    have hτinv : τ⁻¹ c = c := hcF τ⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers τ))
    have hw : t c * c⁻¹ ∈ commV (Subgroup.zpowers t) :=
      Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, c, rfl⟩
    have hτw : τ (t c * c⁻¹) = t c * c⁻¹ := by
      rw [map_mul, map_inv]
      have h1 : τ (t c) = t c := by
        have h2 := congrArg (fun f : MulAut V => f c) hτt
        rw [MulAut.mul_apply, MulAut.mul_apply, hτinv] at h2
        exact h2
      rw [h1, hc]
    have hsup : t c * c⁻¹ ∈ fixV (Y ⊔ Subgroup.zpowers τ) :=
      FixVLat.mem_fixV_sup (fun y hy => hY y hy _ hw)
        (fun z hz => (mem_fixV_zpowers_iff.mpr hτw) z hz)
    have hL : t c * c⁻¹ ∈ fixV L := fixV_anti hgen₁ hsup
    rw [hfix] at hL
    have h1 : t c * c⁻¹ = 1 := Subgroup.mem_bot.mp hL
    rwa [mul_inv_eq_one] at h1
  have hdec : ∀ v : V, t v = v → ∃ c ∈ fixV (Subgroup.zpowers τ),
      ∃ e ∈ commV (Subgroup.zpowers t), v = c * e := by
    intro v htv
    obtain ⟨hsup, -⟩ := coprime_decomp (P := Subgroup.zpowers τ) hoddV hV
      (W := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
    have hv : v ∈ commSub (⊤ : Subgroup V) (Subgroup.zpowers τ) ⊔
        (⊤ ⊓ fixV (Subgroup.zpowers τ)) := by
      rw [hsup]
      exact Subgroup.mem_top v
    obtain ⟨⟨e', he'⟩, ⟨c, hc⟩, hvec⟩ := Subgroup.mem_sup'.mp hv
    have hcF : c ∈ fixV (Subgroup.zpowers τ) := hc.2
    have he'V : e' ∈ commV (Subgroup.zpowers τ) := by rwa [commV_eq_commSub]
    have htc : t c = c := hCa c (mem_fixV_zpowers_iff.mp hcF)
    have hte' : t e' = e' := by
      have h : t e' * t c = e' * c := by rw [← map_mul, hvec, htv]
      rw [htc] at h
      exact mul_right_cancel h
    have hWt : ∀ w ∈ commV (Subgroup.zpowers τ), t w ∈ commV (Subgroup.zpowers τ) := by
      have hmap : (commV (Subgroup.zpowers τ)).map t.toMonoidHom =
          commV (Subgroup.zpowers τ) := by
        rw [← commV_zpowers_conj_eq τ t, htτ, Subgroup.zpowers_inv]
      intro w hw
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hw
    have hWτ : ∀ w ∈ commV (Subgroup.zpowers τ), τ w ∈ commV (Subgroup.zpowers τ) :=
      fun w hw => commV_apply_mem_of_mem (Subgroup.mem_zpowers τ) hw
    have hfree : ∀ w ∈ commV (Subgroup.zpowers τ), τ w = w → w = 1 := by
      intro w hw hτw
      have hwF : w ∈ fixV (Subgroup.zpowers τ) := mem_fixV_zpowers_iff.mpr hτw
      have hmem : w ∈ commV (Subgroup.zpowers τ) ⊓ fixV (Subgroup.zpowers τ) := ⟨hw, hwF⟩
      rw [hτfixbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    obtain ⟨x, -, hxe⟩ := mem_commV_of_fixed hV ht hτ htτ hWt hWτ hfree he'V hte'
    exact ⟨c, hcF, e', Subgroup.subset_closure ⟨t, Subgroup.mem_zpowers t, x, hxe.symm⟩,
      by rw [← hvec, mul_comm]⟩
  have hkey : ∀ v : V, t v = v → u v = v → v ∈ commV (Subgroup.zpowers t) := by
    intro v htv huv
    obtain ⟨c, hcF, e, he, hvec⟩ := hdec v htv
    have huc : u c = c := by
      have h1 : u (c * e) = u c * e := by rw [map_mul, hu_fix e he]
      have h2 : u c * e = c * e := by rw [← h1, ← hvec, huv]
      exact mul_right_cancel h2
    have htc : t c = c := hCa c (mem_fixV_zpowers_iff.mp hcF)
    have hcMem : c ∈ fixV (Subgroup.closure ({t, u, τ} : Set (MulAut V))) := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem y hy =>
        have h1 : y = t ∨ y = u ∨ y = τ := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hy
        rcases h1 with h | h | h
        · rw [h]; exact htc
        · rw [h]; exact huc
        · rw [h]; exact hcF τ (Subgroup.mem_zpowers τ)
      | one => rfl
      | mul a b _ _ ha hb => rw [MulAut.mul_apply, hb, ha]
      | inv a _ ha =>
        have h2 : a ((a⁻¹) c) = a c := by rw [MulAut.apply_inv_self, ha]
        exact a.injective h2
    have hcL : c ∈ fixV L := fixV_anti hgen₂ hcMem
    rw [hfix] at hcL
    have hc1 : c = 1 := Subgroup.mem_bot.mp hcL
    rw [hvec, hc1, one_mul]
    exact he
  rw [commV, Subgroup.closure_le]
  rintro _ ⟨s, hs, x, rfl⟩
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
  rcases CommVZ4.zpow_eq_one_or_self_of_sq hu n with h | h
  · rw [h]
    simp only [MulAut.one_apply, mul_inv_cancel]
    exact (commV (Subgroup.zpowers t)).one_mem
  · rw [h]
    refine hkey (u x * x⁻¹) (hut x) ?_
    exact (commV_zpowers_le_fixV_of_involution hV hu
      (Subgroup.subset_closure ⟨u, Subgroup.mem_zpowers u, x, rfl⟩)) u (Subgroup.mem_zpowers u)

theorem not_commV_le_of_sup {L Y₁ Y₂ : Subgroup (MulAut V)} (hfix : fixV L = ⊥)
    {t u : MulAut V} (hu1 : u ≠ 1)
    (hY₁ : ∀ y ∈ Y₁, ∀ w ∈ commV (zpowers t), y w = w)
    (hY₂ : ∀ y ∈ Y₂, ∀ w ∈ commV (zpowers u), y w = w) (hgen : L ≤ Y₁ ⊔ Y₂) :
    ¬ commV (zpowers u) ≤ commV (zpowers t) := by
  intro hle
  have hsub : commV (Subgroup.zpowers u) ≤ fixV L := by
    intro w hw
    exact fixV_anti hgen (FixVLat.mem_fixV_sup (fun y hy => hY₁ y hy w (hle hw))
      (fun y hy => hY₂ y hy w hw))
  have hbot : commV (Subgroup.zpowers u) = ⊥ :=
    le_bot_iff.mp (by rw [← hfix]; exact hsub)
  have hu1' : u = 1 := by
    ext v
    have hmem : u v * v⁻¹ ∈ commV (Subgroup.zpowers u) :=
      Subgroup.subset_closure ⟨u, Subgroup.mem_zpowers u, v, rfl⟩
    rw [hbot] at hmem
    have h1 : u v * v⁻¹ = 1 := Subgroup.mem_bot.mp hmem
    rwa [mul_inv_eq_one] at h1
  exact hu1 hu1'

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
