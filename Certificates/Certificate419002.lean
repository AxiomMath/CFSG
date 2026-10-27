module

public import Certificates.Data.M11Sylow3
import CFSG.Certificates.Kernel.PermCent.SmallBSound
import Certificates.Kernel.PermCent.K419002
public import Certificates.Data.Kernel.PermCent.CV

public section

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.GH74.KGroups CFSG.Certificates.Kernel.PkCV

namespace Certificates

open CertificateChecks

private theorem map_cOf_ev419002 (L : List (Equiv.Perm (Fin 11))) : L = (L.map cOf).map ev := by
  rw [List.map_map]
  conv_lhs => rw [← List.map_id L]
  exact List.map_congr_left fun σ _ => (ev_cOf σ).symm

private theorem hE419002 : m11Elements = (elemsC m11Certificate).map ev := elemsT_eq_elemsC m11Certificate

private theorem cent_eq419002 : M11Sylow.centCheck () = M11B.centC := by
  rw [M11Sylow.centCheck.eq_1, hE419002, eq_ev_cOf (M11Sylow.pU ()), eq_ev_cOf (M11Sylow.pV ()),
    M11B.centC.eq_1, M11B.E.eq_1, M11B.U.eq_1, M11B.V.eq_1, M11B.EL.eq_1, List.all_map]
  simp only [Function.comp_def, ev_mul', decide_ev_eq, contains_ev]

private theorem cent18_eq419002 : M11Sylow.cent18Check () = M11B.cent18C := by
  rw [M11Sylow.cent18Check.eq_1, hE419002, map_cOf_ev419002 (M11Sylow.pE ()), M11B.cent18C.eq_1,
    M11B.E.eq_1, M11B.EL.eq_1, List.all_map]
  simp only [Function.comp_def, List.filter_map, List.length_map, ev_mul', decide_ev_eq,
    one_eq_ev]

private theorem move_eq419002 : M11Sylow.moveCheck () = M11B.moveC := by
  have o5 : ∀ g : CV 11, orderIs g 5 = orderIsP g 5 [5] :=
    fun g => orderIs_eq_P g 5 [5] (by norm_num) (by decide) (by decide)
  have o11 : ∀ g : CV 11, orderIs g 11 = orderIsP g 11 [11] :=
    fun g => orderIs_eq_P g 11 [11] (by norm_num) (by decide) (by decide)
  rw [M11Sylow.moveCheck.eq_1, hE419002, M11B.moveC.eq_1, M11B.E.eq_1, List.all_map]
  simp only [Function.comp_def, orderIs_ev, o5, o11]

theorem certificate419002 : CFSG.Sporadic.Schreier.M11Sylow.centCheck () = true ∧
    CFSG.Sporadic.Schreier.M11Sylow.cent18Check () = true ∧
    CFSG.Sporadic.Schreier.M11Sylow.moveCheck () = true := by
  rw [cent_eq419002, cent18_eq419002, move_eq419002]
  exact ⟨KernelPermCent.k419002_cent, KernelPermCent.k419002_cent18, KernelPermCent.k419002_move⟩

end Certificates
