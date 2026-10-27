module

public import CFSG.Quasithin.EmptyFaithful.A38c10Env
public import CFSG.Quasithin.EmptyFaithful.SzC4NdVMain
public import CFSG.Quasithin.EmptyFaithful.SzC4NdDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.A38c10

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.Quasithin CFSG.Quasithin.FLc CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.InternalSec CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped commutatorElement IsMulCommutative

section Transport2

variable {G : Type} [Group G] [Finite G] {L S R Yp Y₁ Y₂ Vp : Subgroup G}

theorem Env4.rho_mem_autOn_iff (E : Env4 L S R Yp Y₁ Y₂ Vp) (l : ↥L) :
    Setup.rho Vp L E.L_N l ∈ autOn (S ⊓ L) Vp ↔ (l : G) ∈ S ⊓ L := by
  have hLN := E.L_N
  have hker : ∀ l : ↥L, Setup.rho Vp L hLN l = 1 → (l : G) ∈ S ⊓ L := fun l h =>
    E.ker_le ⟨l.2, (Setup.rho_eq_one_iff hLN l).1 h⟩
  constructor
  · intro hl
    obtain ⟨g, hg, hgl⟩ := Setup.mem_autOn_iff.1 hl
    have hgL : (g : G) ∈ L := hg.2
    have h1 : Setup.rho Vp L hLN ⟨g, hgL⟩ = Setup.rho Vp L hLN l := by rw [← hgl]; rfl
    have h2 : Setup.rho Vp L hLN (⟨g, hgL⟩⁻¹ * l) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 := hker _ h2
    have h4 : (l : G) = (g : G) * ((⟨g, hgL⟩⁻¹ * l : ↥L) : G) := by simp
    rw [h4]
    exact (S ⊓ L).mul_mem hg h3
  · intro hl
    exact Setup.mem_autOn_iff.2 ⟨⟨l, hLN l.2⟩, hl, rfl⟩

theorem msGat_of_msDataAt (E : Env4 L S R Yp Y₁ Y₂ Vp) {P : Subgroup (MulAut ↥Vp)}
    {ψ : ↥P →* SLt 3} {q : ↥Vp}
    (hms : @MSDataAt ↥Vp (commGroupOfElemAbelian E.Vp_elem) (autOn L Vp) (autOn (S ⊓ L) Vp)
      (autOn S Vp) (autOn Y₁ Vp) (autOn Y₂ Vp)
      (@commV ↥Vp (commGroupOfElemAbelian E.Vp_elem) (autOn L Vp)) P ψ q)
    {PG : Subgroup G} (hPGL : PG ≤ L)
    (hmemPG : ∀ l : ↥L, (l : G) ∈ PG ↔ Setup.rho Vp L E.L_N l ∈ P) :
    ∃ ψ' : ↥PG →* SLt 3, MSGat L S Vp Yp Y₁ Y₂ PG ψ' (q : G) := by
  classical
  have hcomm : IsMulCommutative ↥Vp := E.Vp_elem.1
  have hLN := E.L_N
  obtain ⟨hBP, hPΛ, hPne, hWP, hmin, hYP, hψs, hψk, hqU, hq1, hqP, hqc⟩ := hms
  set ρ : ↥L →* MulAut ↥Vp := Setup.rho Vp L hLN with hρ
  have hρΛ : ∀ φ ∈ autOn L Vp, ∃ l : ↥L, ρ l = φ := fun φ hφ =>
    (Setup.mem_autOn_self_iff hLN).1 hφ
  have hρmem : ∀ l : ↥L, ρ l ∈ autOn L Vp := fun l => (Setup.mem_autOn_self_iff hLN).2 ⟨l, rfl⟩
  have hρconj : ∀ l : ↥L, ρ l = conjAct Vp ⟨(l : G), hLN l.2⟩ := fun l => rfl
  have hBmem : ∀ l : ↥L, (l : G) ∈ S ⊓ L → ρ l ∈ autOn (S ⊓ L) Vp := fun l hl =>
    (E.rho_mem_autOn_iff l).2 hl
  have hBinv : ∀ l : ↥L, ρ l ∈ autOn (S ⊓ L) Vp → (l : G) ∈ S ⊓ L := fun l hl =>
    (E.rho_mem_autOn_iff l).1 hl
  have hker : ∀ l : ↥L, ρ l = 1 → (l : G) ∈ S ⊓ L := fun l h =>
    E.ker_le ⟨l.2, (Setup.rho_eq_one_iff hLN l).1 h⟩
  have hYp₁ : Y₁ ≤ L := E.Y₁_Yp.trans E.Yp_L
  have hYp₂ : Y₂ ≤ L := E.Y₂_Yp.trans E.Yp_L
  let φ : ↥PG →* ↥P :=
    (ρ.comp (Subgroup.inclusion hPGL)).codRestrict P
      (fun x => (hmemPG (Subgroup.inclusion hPGL x)).1 x.2)
  refine ⟨ψ.comp φ, hPGL, ?_, ?_, ?_, ?_, ?_, ?_, ?_, q.2, ?_, ?_, ?_⟩
  · intro x hx
    exact (hmemPG ⟨x, hx.2⟩).2 (hBP (hBmem ⟨x, hx.2⟩ hx))
  · intro h
    apply hPne
    refine le_antisymm hPΛ fun φ' hφ' => ?_
    obtain ⟨l, rfl⟩ := hρΛ φ' hφ'
    exact (hmemPG l).1 (by rw [h]; exact l.2)
  · intro s hs p hp
    have hsN : s ∈ Subgroup.normalizer (Vp : Set G) := E.S_N hs
    have hsp : s * p * s⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (E.S_L hs) p).mp (hPGL hp)
    have hmem' : conjAct Vp ⟨s, hsN⟩ ∈ autOn S Vp := Setup.mem_autOn_iff.2 ⟨⟨s, hsN⟩, hs, rfl⟩
    have hp' : ρ ⟨p, hPGL hp⟩ ∈ P := (hmemPG ⟨p, hPGL hp⟩).1 hp
    have e : ρ ⟨s * p * s⁻¹, hsp⟩ =
        conjAct Vp ⟨s, hsN⟩ * ρ ⟨p, hPGL hp⟩ * (conjAct Vp ⟨s, hsN⟩)⁻¹ := by
      rw [hρconj ⟨p, hPGL hp⟩, hρconj ⟨s * p * s⁻¹, hsp⟩, ← map_inv, ← map_mul, ← map_mul]
      rfl
    exact (hmemPG ⟨s * p * s⁻¹, hsp⟩).2 (by rw [e]; exact hWP _ hmem' _ hp')
  · intro X hSX hXL hXne hYX hPX
    refine hmin (autOn X Vp) (autOn_le_autOn_of_le hSX) (autOn_le_autOn_of_le hXL) ?_
      (sup_le (autOn_le_autOn_of_le (E.Y₁_Yp.trans hYX))
        (autOn_le_autOn_of_le (E.Y₂_Yp.trans hYX))) ?_
    · intro h
      apply hXne
      refine le_antisymm hXL fun l hl => ?_
      have h1 : ρ ⟨l, hl⟩ ∈ autOn X Vp := h ▸ hρmem ⟨l, hl⟩
      obtain ⟨x, hxX, hx⟩ := Setup.mem_autOn_iff.1 h1
      have hxL : (x : G) ∈ L := hXL hxX
      have h2 : ρ (⟨x, hxL⟩⁻¹ * ⟨l, hl⟩) = 1 := by
        have : ρ ⟨x, hxL⟩ = ρ ⟨l, hl⟩ := by rw [← hx]; rfl
        rw [map_mul, map_inv, this, inv_mul_cancel]
      have h3 := hker _ h2
      have h4 : l = (x : G) * ((⟨x, hxL⟩⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
      rw [h4]
      exact X.mul_mem hxX (hSX h3)
    · intro φ' hφ'
      obtain ⟨l, rfl⟩ := hρΛ φ' (hPΛ hφ')
      have hlX : (l : G) ∈ X := hPX ((hmemPG l).2 hφ')
      exact Setup.mem_autOn_iff.2 ⟨⟨l, hLN l.2⟩, hlX, rfl⟩
  · rcases hYP with h | h
    · refine Or.inl fun y hy => ?_
      exact (hmemPG ⟨y, hYp₁ hy⟩).2 (h (Setup.mem_autOn_iff.2 ⟨⟨y, hLN (hYp₁ hy)⟩, hy, rfl⟩))
    · refine Or.inr fun y hy => ?_
      exact (hmemPG ⟨y, hYp₂ hy⟩).2 (h (Setup.mem_autOn_iff.2 ⟨⟨y, hLN (hYp₂ hy)⟩, hy, rfl⟩))
  · intro t
    obtain ⟨p, hp⟩ := hψs t
    obtain ⟨l, hl⟩ := hρΛ p (hPΛ p.2)
    have hlPG : (l : G) ∈ PG := (hmemPG l).2 (by rw [hl]; exact p.2)
    refine ⟨⟨l, hlPG⟩, ?_⟩
    show ψ (φ ⟨l, hlPG⟩) = t
    have : φ ⟨l, hlPG⟩ = p := Subtype.ext hl
    rw [this]
    exact hp
  · intro x hx
    have h1 : ((φ x : ↥P) : MulAut ↥Vp) ∈ autOn (S ⊓ L) Vp := hψk (φ x) hx
    exact hBinv ⟨x, hPGL x.2⟩ h1
  · intro h
    exact hq1 (Subtype.ext h)
  · intro a ha
    have h1 := congrArg Subtype.val (hqP (ρ ⟨a, hPGL ha⟩) ((hmemPG ⟨a, hPGL ha⟩).1 ha))
    rw [hρconj, Setup.coe_conjAct_apply] at h1
    exact h1
  · have hK : oTwoUpper P ≤ autOn (oTwoUpper PG) Vp := by
      refine (Subgroup.closure_le _).2 ?_
      rintro x ⟨hxP, hodd⟩
      obtain ⟨l, rfl⟩ := hρΛ x (hPΛ hxP)
      have hlPG : (l : G) ∈ PG := (hmemPG l).2 hxP
      obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper PG hlPG
      have hmem : ρ l ^ 2 ^ k ∈ autOn (oTwoUpper PG) Vp := by
        rw [← map_pow]
        exact Setup.mem_autOn_iff.2 ⟨⟨(l : G) ^ 2 ^ k, hLN (L.pow_mem l.2 _)⟩, hk, rfl⟩
      have hcop : Nat.Coprime (2 ^ k) (orderOf (ρ l)) :=
        Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hodd)
      exact (Subgroup.zpowers_le.2 hmem) (A4.mem_zpowers_pow_of_coprime hcop)
    have hKN : oTwoUpper PG ≤ Subgroup.normalizer (Vp : Set G) :=
      (oTwoUpper_le PG).trans (hPGL.trans hLN)
    have hmono : commV (oTwoUpper P) ≤ commV (autOn (oTwoUpper PG) Vp) :=
      Subgroup.closure_mono fun w ⟨x, hx, v, h⟩ => ⟨x, hK hx, v, h⟩
    have := hmono hqc
    rw [commV_autOn_eq1527d hKN] at this
    exact this

theorem msg2_of_msData2 (E : Env4 L S R Yp Y₁ Y₂ Vp)
    (hms : @MSData2 ↥Vp (commGroupOfElemAbelian E.Vp_elem) (autOn L Vp) (autOn (S ⊓ L) Vp)
      (autOn S Vp) (autOn Y₁ Vp) (autOn Y₂ Vp)
      (@commV ↥Vp (commGroupOfElemAbelian E.Vp_elem) (autOn L Vp))) :
    MSG2 L S Vp Yp Y₁ Y₂ := by
  classical
  obtain ⟨D, P₁, P₃, hD₁, hD₃, ⟨ψ₁, q₁, h₁⟩, ⟨ψ₃, q₃, h₃⟩⟩ := hms
  have hLN := E.L_N
  let α : ↥L →* SLt 4 := D.e.toMonoidHom.comp (autOnHom hLN)
  have hαe : ∀ l : ↥L, α l = D.e (autOnHom hLN l) := fun l => rfl
  have hρ : ∀ l : ↥L, ((autOnHom hLN l : ↥(autOn L Vp)) : MulAut ↥Vp) = Setup.rho Vp L hLN l :=
    fun l => rfl
  have hmem : ∀ (k : ℕ) (P : Subgroup (MulAut ↥Vp)), D.model P = QI 4 {k} → ∀ l : ↥L,
      (l : G) ∈ Pof L α k ↔ Setup.rho Vp L hLN l ∈ P := by
    intro k P hP l
    rw [mem_Pof, hαe, ← hP, D.mem_model, hρ]
  refine ⟨α, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    obtain ⟨x, rfl⟩ := D.e.surjective s
    obtain ⟨l, rfl⟩ := autOnHom_surjective hLN x
    exact ⟨l, rfl⟩
  · rw [← ker_autOnHom_eq_pCore1527d hLN E.O2L E.kerP]
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hαe]
    exact map_eq_one_iff _ D.e.injective
  · intro l
    rw [hαe, ← D.model_B, D.mem_model, hρ]
    exact (E.rho_mem_autOn_iff l).symm
  · obtain ⟨ψ', hψ'⟩ := msGat_of_msDataAt E h₁ (Pof_le L α 1) (hmem 1 P₁ hD₁)
    exact ⟨ψ', (q₁ : G), hψ'⟩
  · obtain ⟨ψ', hψ'⟩ := msGat_of_msDataAt E h₃ (Pof_le L α 3) (hmem 3 P₃ hD₃)
    exact ⟨ψ', (q₃ : G), hψ'⟩

end Transport2

end CFSG.Quasithin.A38c10
