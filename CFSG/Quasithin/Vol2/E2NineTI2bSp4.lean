module

public import CFSG.Quasithin.Vol2.E2NineTI2bSp4Dich
public import CFSG.Quasithin.Vol2.E2NineTI2bSp4Coord
public import CFSG.Quasithin.Vol2.E2NineTI2bSp4Four
public import CFSG.Quasithin.Vol2.E2SevenKG7Large
public import CFSG.Quasithin.Vol2.E2NineTI2bBase

public section

namespace CFSG.Quasithin.E2.TI2b.Sp4

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.Quasithin.SteinbergBS (rootLong rootShort)
open CFSG.Quasithin.Ch3E213M

theorem conjSub_map_of_conj {G G' : Type} [Group G] [Group G'] (φ : G →* G') (σ : G →* G)
    (t : G') (h : ∀ a, t * φ a * t⁻¹ = φ (σ a)) (X : Subgroup G) :
    conjSub t (X.map φ) = (X.map σ).map φ := by
  ext z
  constructor
  · intro hz
    rw [mem_conjSub] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨σ x, ⟨x, hx, rfl⟩, ?_⟩
    rw [← h x, hxz]
    group
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    rw [mem_conjSub]
    refine ⟨x, hx, ?_⟩
    rw [← h x]
    group

theorem conjSub_map {G G' : Type} [Group G] [Group G'] (φ : G →* G') (y : G) (X : Subgroup G) :
    conjSub (φ y) (X.map φ) = (conjSub y X).map φ := by
  ext z
  constructor
  · intro hz
    rw [mem_conjSub] at hz
    obtain ⟨x, hx, hxz⟩ := hz
    refine ⟨y * x * y⁻¹, mem_conjSub.mpr (by simpa [mul_assoc] using hx), ?_⟩
    rw [map_mul, map_mul, map_inv, hxz]
    group
  · rintro ⟨w, hw, rfl⟩
    have hw' : y⁻¹ * w * y ∈ X := mem_conjSub.mp (SetLike.mem_coe.mp hw)
    rw [mem_conjSub]
    exact ⟨y⁻¹ * w * y, hw', by rw [map_mul, map_mul, map_inv]⟩

variable {k : Type} [Field k] [CharP k 2]

theorem rootLong_comm {a b : antiSp k} (ha : a ∈ rootLong k) (hb : b ∈ rootLong k) :
    a * b = b * a :=
  antiUnipotentCenter_comm (CFSG.Quasithin.SteinbergBS.rootLong_le_center ha)
    (antiUnipotentCenter_le (CFSG.Quasithin.SteinbergBS.rootLong_le_center hb))

theorem exists_mul_of_sup_eq_top {A : Type} [Group A] {K Ts : Subgroup A} [K.Normal]
    (h : K ⊔ Ts = ⊤) (x : A) : ∃ κ ∈ K, ∃ s ∈ Ts, κ * s = x := by
  have hxK : x ∈ K ⊔ Ts := h ▸ Subgroup.mem_top x
  have h1 : x ∈ ((K ⊔ Ts : Subgroup A) : Set A) := hxK
  rw [Subgroup.normal_mul] at h1
  obtain ⟨κ, hκ, s, hs, h⟩ := Set.mem_mul.mp h1
  exact ⟨κ, hκ, s, hs, h⟩

theorem sp4Leaf_holds : Sp4Leaf := by
  intro A _ _ Ts Ms K Es _ n hn2 hE28 hker hC hLT hSp hMK hMsE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTs : IsSylowTwoOf Ts ⊤ := hE28.minParabolic.isSylow
  have hEsP : IsPGroup 2 Es := B6.isPGroup_of_isElemAbelian hE28.elem
  have hV4 : 4 ≤ Nat.card Es := four_le_card_of_sp4 hn2 hTs hC hSp hMK hMsE hEsP hE28.ne_bot
  have hKN : Subgroup.normalizer (K : Set A) = ⊤ := Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hXN : (⊤ : Subgroup A) ≤ Subgroup.normalizer (K : Set A) := by rw [hKN]
  have hC' : (⊤ : Subgroup A) ⊓ Subgroup.centralizer (K : Set A) = ⊥ := by
    rw [top_inf_eq]
    exact hC
  obtain ⟨k, _, _, _, hk, ⟨D⟩⟩ := exists_sp4Data_of_kg7 hE28 hker le_top hXN hC' hLT hn2 hSp hV4
  have hMX : Ms ≤ (⊤ : Subgroup A) := le_top
  obtain ⟨φ, hφi, hφr, hφc, hφsw⟩ := exists_coordEmb_conj D hker hMX (le_top : K ≤ ⊤)
  obtain ⟨hT, hM⟩ := comap_coordEmb_M D hφi hφr hφc (le_top : Ts ≤ ⊤) hMK
  have hk4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hEK : Es ≤ K := le_of_sp4Data D hker hMX le_top
  have hEW : Es.comap φ = coordIn D.θ Es := hφc Es le_top
  have hmapcomap : ∀ X : Subgroup A, X ≤ K → (X.comap φ).map φ = X := fun X hX =>
    Subgroup.map_comap_eq_self (by rw [hφr]; exact hX)
  have hMsφ : ∀ b ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)), φ b ∈ Ms := by
    intro b hb
    have : b ∈ Ms.comap φ := by rw [hM]; exact hb
    exact this
  have hWinv : ∀ b ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)),
      ∀ w ∈ Es.comap φ, b * w * b⁻¹ ∈ Es.comap φ := by
    intro b hb w hw
    rw [Subgroup.mem_comap] at hw ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hMsE (hMsφ b hb)) (φ w)).mp hw
  have hWU : Es.comap φ ≤ antiUnipotentCenter k := hEW ▸ D.V_le_center
  have hWeq : Es.comap φ = antiUnipotentCenter k := by
    rcases borelInvariant_center hk4 hWU hWinv with h | h | h | h
    · exfalso
      apply hE28.ne_bot
      rw [← hmapcomap Es hEK, h, Subgroup.map_bot]
    · exfalso
      apply D.V_not_le_long
      rw [← hEW, h]
    · exfalso
      apply D.V_not_le_short
      rw [← hEW, h]
    · exact h
  have hW : rootLong k ≤ Es.comap φ := by
    rw [hWeq]
    exact CFSG.Quasithin.SteinbergBS.rootLong_le_center
  set R₀ := (rootLong k).map φ with hR₀
  have hR₀E : R₀ ≤ Es := by
    rw [hR₀, Subgroup.map_le_iff_le_comap]
    exact hW
  have hR₀K : R₀ ≤ K := by
    rw [← hφr]
    rintro _ ⟨z, -, rfl⟩
    exact ⟨z, rfl⟩
  have hcard : Nat.card R₀ = 2 ^ n := by
    rw [hR₀, Subgroup.card_map_of_injective hφi, CFSG.Quasithin.SteinbergBS.card_rootLong, hk]
  have hR₀ne : R₀ ≠ ⊥ := by
    intro h0
    have h1 : Nat.card R₀ = 1 := by rw [h0]; exact Subgroup.card_bot
    have h2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hR₀comap : R₀.comap φ = rootLong k := Subgroup.comap_map_eq_self_of_injective hφi _
  have hTsMs : Ts ≤ Ms := hE28.minParabolic.le
  have hTsE : Ts ≤ Subgroup.normalizer (Es : Set A) := fun s hs => hMsE (hTsMs hs)
  have hconj : ∀ s ∈ Ts, conjSub s R₀ = R₀ ∨ conjSub s R₀ = (rootShort k).map φ := by
    intro s hs
    have hsM : s ∈ Ms := hTsMs hs
    have hR₁K : conjSub s R₀ ≤ K := fun z hz => by
      have h1 := hR₀K (mem_conjSub.mp hz)
      have h2 := (inferInstance : K.Normal).conj_mem _ h1 s
      simpa [mul_assoc] using h2
    have hR₁E : conjSub s R₀ ≤ Es := fun z hz => by
      have h1 := hR₀E (mem_conjSub.mp hz)
      have h2 := (Subgroup.mem_normalizer_iff.mp (hTsE hs) (s⁻¹ * z * s)).mp h1
      simpa [mul_assoc] using h2
    set W := (conjSub s R₀).comap φ with hWdef
    have hWmap : W.map φ = conjSub s R₀ :=
      Subgroup.map_comap_eq_self (by rw [hφr]; exact hR₁K)
    have hWle : W ≤ antiUnipotentCenter k := by
      rw [← hWeq]
      exact Subgroup.comap_mono hR₁E
    have hWinv' : ∀ b ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)),
        ∀ w ∈ W, b * w * b⁻¹ ∈ W := by
      intro b hb w hw
      have hw' : φ w ∈ conjSub s R₀ := hw
      have hw'' : s⁻¹ * φ w * s ∈ R₀ := mem_conjSub.mp hw'
      have hφbK : φ b ∈ K := by
        rw [← hφr]
        exact ⟨b, rfl⟩
      have hcK : s⁻¹ * φ b * s ∈ K := by
        have := (inferInstance : K.Normal).conj_mem (φ b) hφbK s⁻¹
        simpa using this
      obtain ⟨b', hb'⟩ : s⁻¹ * φ b * s ∈ φ.range := by
        rw [hφr]
        exact hcK
      have hb'N : b' ∈ Subgroup.normalizer (antiUnipotent k : Set (antiSp k)) := by
        rw [← hM]
        show φ b' ∈ Ms
        rw [hb']
        exact Ms.mul_mem (Ms.mul_mem (Ms.inv_mem hsM) (hMsφ b hb)) hsM
      obtain ⟨a, ha, haφ⟩ : ∃ a ∈ rootLong k, φ a = s⁻¹ * φ w * s := hw''
      show φ (b * w * b⁻¹) ∈ conjSub s R₀
      rw [mem_conjSub]
      have e : s⁻¹ * φ (b * w * b⁻¹) * s = φ (b' * a * b'⁻¹) := by
        simp only [map_mul, map_inv]
        rw [hb', haφ]
        group
      rw [e]
      exact ⟨b' * a * b'⁻¹, CFSG.Quasithin.SteinbergBS.conj_mem_rootLong hb'N ha, rfl⟩
    have hWne : W ≠ ⊥ := by
      intro h0
      apply hR₀ne
      have h1 : conjSub s R₀ = ⊥ := by rw [← hWmap, h0, Subgroup.map_bot]
      have h2 : conjSub s R₀ = conjSub s ⊥ := by rw [h1, (conjSub s).map_bot]
      exact (conjSub s).injective h2
    rcases borelInvariant_center hk4 hWle hWinv' with h0 | h0 | h0 | h0
    · exact absurd h0 hWne
    · left
      rw [← hWmap, h0]
    · right
      rw [← hWmap, h0]
    · exfalso
      have hR1 : conjSub s R₀ = Es := by
        rw [← hWmap, h0, ← hWeq, hmapcomap Es hEK]
      have hR0 : R₀ = Es := by
        have h1 := congrArg (conjSub s⁻¹) hR1
        rw [← conjSub_mul, inv_mul_cancel, conjSub_one,
          conjSub_eq_self (hTsE (Ts.inv_mem hs))] at h1
        exact h1
      apply D.V_not_le_long
      rw [← hEW, ← hR0, hR₀comap]
  obtain ⟨s₀, hs₀, g, j, -, hact, -, hss, -⟩ := D.swap
  obtain ⟨t, htT, ht⟩ := hφsw s₀ hs₀ (MulAut.conj g * minorAut k ^ j) hact
  set σ : MulAut (antiSp k) := MulAut.conj g * minorAut k ^ j with hσ
  refine ⟨R₀, hR₀E, hR₀K, hcard, ?_⟩
  set 𝓡 : Set (Subgroup A) :=
    {R | ∃ y : antiSp k, R = (conjSub y (rootLong k)).map φ} with h𝓡
  refine starDich_of_swap inferInstance hR₀K htT 𝓡 ?_ ?_
  · intro x _
    obtain ⟨κ, hκ, s, hs, rfl⟩ := exists_mul_of_sup_eq_top hLT x
    obtain ⟨y, rfl⟩ : κ ∈ φ.range := by rw [hφr]; exact hκ
    rcases hconj s hs with h1 | h1
    · left
      refine ⟨y, ?_⟩
      rw [conjSub_mul, h1, hR₀, conjSub_map]
    · right
      refine ⟨σ y, ?_⟩
      have e : (conjSub y (rootShort k)).map σ.toMonoidHom = conjSub (σ y) (rootLong k) := by
        rw [← conjSub_map σ.toMonoidHom y (rootShort k), hss]
        rfl
      rw [conjSub_mul, h1, conjSub_map, conjSub_map_of_conj φ σ.toMonoidHom t (fun a => ht a), e]
  · rintro R ⟨y, rfl⟩ hRT hRK Y hYK hCY
    have hRY : (conjSub y (rootLong k)).map φ ≤ Y := by
      intro r hr
      apply hCY
      refine ⟨⟨hRT hr, hRK hr⟩, ?_⟩
      show r ∈ Subgroup.centralizer (((conjSub y (rootLong k)).map φ : Subgroup A) : Set A)
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨b, hb, rfl⟩
      obtain ⟨a, ha, rfl⟩ := hr
      have ha' : y⁻¹ * a * y ∈ rootLong k := mem_conjSub.mp ha
      have hb' : y⁻¹ * b * y ∈ rootLong k := mem_conjSub.mp hb
      have hc := rootLong_comm hb' ha'
      have hba : b * a = a * b := by
        have h1 : y * (y⁻¹ * b * y * (y⁻¹ * a * y)) * y⁻¹ =
            y * (y⁻¹ * a * y * (y⁻¹ * b * y)) * y⁻¹ := by rw [hc]
        simpa [mul_assoc] using h1
      rw [← map_mul, ← map_mul, hba]
    have hY' : conjSub y (rootLong k) ≤ Y.comap φ := fun a ha => hRY ⟨a, ha, rfl⟩
    have hY'' : rootLong k ≤ conjSub y⁻¹ (Y.comap φ) := by
      intro a ha
      rw [mem_conjSub, inv_inv]
      apply hY'
      rw [mem_conjSub]
      simpa [mul_assoc] using ha
    have hd := dich_rootLong hk4 hY''
    have key : conjSub y (conjSub y⁻¹ (Y.comap φ)) = Y.comap φ := by
      rw [← conjSub_mul, mul_inv_cancel, conjSub_one]
    have hd' : Dich (conjSub y (rootLong k)) (Y.comap φ) := by
      have := dich_conj (x := y) (R := rootLong k) (Y := conjSub y⁻¹ (Y.comap φ))
      rw [key] at this
      exact this.mpr hd
    have hYmap : (Y.comap φ).map φ = Y := by
      apply Subgroup.map_comap_eq_self
      rw [hφr]
      exact hYK
    exact dich_of_embedding hφi rfl hYmap hd'

end CFSG.Quasithin.E2.TI2b.Sp4
